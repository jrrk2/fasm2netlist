// Per-register equivalence between two structural netlists, through whatever
// SAT or SMT solver you point it at.
//
// Both sides' cones are built over the same variable names -- primary inputs
// by port name, register state by the net the register drives -- so a matched
// pair's miter asks whether the two next-state functions differ for ANY input
// and ANY state.  That is the question yosys's equiv_simple asks per point,
// and the one a plain equiv_miter does not: without the shared symbols a
// solver is free to start the two designs in different states and every
// register "differs".
#include "lvs/boolnet.hpp"
#include "lvs/cone.hpp"
#include "lvs/netlist.hpp"
#include "lvs/solver.hpp"
#include "lvs/regmap.hpp"
#include "dsp_ports.hpp"

#include <algorithm>
#include <atomic>
#include <chrono>
#include <fstream>
#include <iostream>
#include <memory>
#include <thread>
#include "json.hpp"

#include <regex>
#include <sstream>
#include <string>

using namespace lvs;

namespace {

void usage()
{
    std::cerr << "usage: lvs_equiv --gold <a.v|a.json> --gate <b.v|b.json> [--top NAME]\n"
                 "                 [--solver libcadical|libz3|'cmd'] [--format dimacs|smt2]\n"
                 "                 [--dump-prefix PATH] [--quiet] [--explain] [--only TEXT] [--jobs N]\n"
                 "                 [--map FILE: gold<TAB>gate name pairs] [--invert FILE: gold labels whose gate register is stored inverted]\n"
                 "                 [--pair-memories: pair the two sides' RAM/DSP cuts by their boundary functions (two syntheses, no placement)]\n"
                 "\n"
                 "  --jobs N        solve the questions on N sessions in parallel (default: the hardware threads)\n"
                 "  --solver libcadical  the linked CaDiCaL (default when built with it)\n"
              "  --solver libz3  the linked library, one incremental session"
              << (have_linked_z3() ? (have_linked_cadical() ? "\n" : " (default)\n") : " -- NOT IN THIS BUILD\n")
              << "  --solver <cmd>  any binary reading the chosen format, run per question\n";
}

// Which named variables a literal's cone reads.
std::set<std::string> support_of(const BoolNet &net, Lit l)
{
    std::map<uint32_t, std::string> input_of;
    for (const auto &n : net.input_order()) input_of[node_of(net.input_lit(n))] = n;
    std::set<std::string> out;
    std::vector<uint32_t> stack{node_of(l)};
    std::set<uint32_t> seen;
    while (!stack.empty()) {
        uint32_t n = stack.back();
        stack.pop_back();
        if (n == 0 || !seen.insert(n).second) continue;
        auto in = input_of.find(n);
        if (in != input_of.end()) { out.insert(in->second); continue; }
        auto a = net.ands().find(n);
        if (a == net.ands().end()) continue;
        stack.push_back(node_of(a->second.a));
        stack.push_back(node_of(a->second.b));
    }
    return out;
}

std::string emit(const BoolNet &net, Lit target, Format fmt)
{
    std::ostringstream os;
    if (fmt == Format::Dimacs)
        write_dimacs(net, target, os);
    else
        write_smtlib2(net, target, os);
    return os.str();
}

} // namespace

static int run(int argc, char **argv)
{
    std::string gold_path, gate_path, top = "top", gold_top, gate_top, dump_prefix, map_path;
    std::vector<std::pair<std::string, std::string>> compare;   // arbitrary net pairs
    std::string placement_p, gold_json_p, db, device;
    std::string invert_p;   // --invert: gold labels whose gate register holds the complement
    // --pair-memories: no placement says which gate memory is which gold one, so pair their read
    // symbols by proving the boundaries equal (two syntheses of the same RTL, no bitstream).
    bool pair_mem = false;
    Solver solver{have_linked_cadical() ? linked_cadical_name() : have_linked_z3() ? linked_z3_name() : "z3", Format::SmtLib2};
    bool quiet = false;
    // --explain: after a failure, say which named variables each side reads.
    bool explain = false;
    // --only TEXT: check just the registers whose name contains TEXT, for
    // going back to a failure without re-proving everything around it.
    std::string only;
    // --jobs N: the questions are independent, so N sessions over the one
    // network answer them N at a time.  Each session is its own solver with
    // its own learned clauses; the network is read-only while they run.
    int jobs = int(std::max(1u, std::thread::hardware_concurrency()));

    for (int i = 1; i < argc; i++) {
        std::string a = argv[i];
        auto next = [&]() { return (i + 1 < argc) ? std::string(argv[++i]) : std::string(); };
        if (a == "--gold") gold_path = next();
        else if (a == "--gate") gate_path = next();
        else if (a == "--top") top = next();
        else if (a == "--gold-top") gold_top = next();
        else if (a == "--gate-top") gate_top = next();
        else if (a == "--solver") solver.command = next();
        else if (a == "--dump-prefix") dump_prefix = next();
        else if (a == "--explain") explain = true;
        else if (a == "--map") map_path = next();
        else if (a == "--invert") invert_p = next();
        else if (a == "--pair-memories") pair_mem = true;
        else if (a == "--compare") { std::string g = next(); compare.push_back({g, next()}); }
        else if (a == "--placement") placement_p = next();
        else if (a == "--gold-json") gold_json_p = next();
        else if (a == "--db") db = next();
        else if (a == "--device") device = next();
        else if (a == "--quiet") quiet = true;
        else if (a == "--only") only = next();
        else if (a == "--jobs") jobs = std::max(1, atoi(next().c_str()));
        else if (a == "--format") solver.format = (next() == "dimacs") ? Format::Dimacs : Format::SmtLib2;
        else { usage(); return 2; }
    }
    if (gold_path.empty() || gate_path.empty()) { usage(); return 2; }

    // The gold side may be the synthesis's own JSON, which then also names its
    // registers (--gold-json): nothing has to turn it into Verilog first
    auto ends_with = [](const std::string &s, const std::string &x) {
        return s.size() >= x.size() && s.compare(s.size() - x.size(), x.size(), x) == 0;
    };
    const bool gold_is_json = ends_with(gold_path, ".json");
    const bool gate_is_json = ends_with(gate_path, ".json");
    if (gold_is_json && gold_json_p.empty()) gold_json_p = gold_path;
    Netlist gold_nl, gate_nl;
    try {
        gold_nl = gold_is_json ? parse_json_netlist_file(gold_path) : parse_verilog_file(gold_path);
        gate_nl = ends_with(gate_path, ".json") ? parse_json_netlist_file(gate_path) : parse_verilog_file(gate_path);
    } catch (const std::exception &e) {
        std::cerr << "parse error: " << e.what() << "\n";
        return 2;
    }
    const Module *gold_m = gold_nl.find(gold_top.empty() ? top : gold_top);
    const Module *gate_m = gate_nl.find(gate_top.empty() ? top : gate_top);
    if (!gold_m || !gate_m) {
        std::cerr << "module " << top << " not found in both netlists\n";
        return 2;
    }

    // gold_name <TAB> gate_name.  Both sides' cones are built over one symbol
    // table, so renaming the gate's symbols to the gold's names is what makes a
    // miter between them ask about the same variables.  Without it the two
    // netlists share no names at all and every register "differs".
    std::map<std::string, std::string> gate_to_gold;
    std::map<std::string, std::string> mem_cuts;   // gate read symbol -> gold's
    std::map<std::string, std::string> bufg_site;  // gold BUFG cell -> its BUFGCTRL site
    std::map<std::string, std::string> bufg_src;   // BUFGCTRL site -> "<tile> <pin>" of its input in the synthesis
    std::map<std::string, lvs::RegMap::HardBlock> hard_blocks;
    std::map<std::string, std::vector<std::string>> gate_alts;  // other names for the same net

    // Build the register correspondence here rather than in a helper script:
    // it is a filter on this program's own input, and it needs nothing but the
    // placement, the gold netlist and the database.
    if (!placement_p.empty() && !gold_json_p.empty() && !db.empty()) {
        lvs::RegMap rm = lvs::build_regmap(placement_p, gold_json_p, db, device);
        auto sanitise = [](const std::string &in) {
            std::string r;
            for (char c : in) r.push_back(isalnum((unsigned char)c) ? c : '_');
            return r;
        };
        for (const auto &kv : rm.net) gate_to_gold[sanitise(kv.first)] = kv.second;
        for (const auto &kv : rm.alt) gate_alts[sanitise(kv.first)] = kv.second;
        mem_cuts = rm.mem;
        bufg_site = rm.bufg_site;
        bufg_src = rm.bufg_src;
        hard_blocks = rm.hard;
        if (!mem_cuts.empty())
            std::cout << "memory map: " << mem_cuts.size() << " read symbols from the placement\n";
        std::cout << "register map: " << rm.mapped << " from the placement";
        if (rm.skipped) std::cout << ", " << rm.skipped << " unmapped";
        std::cout << " (gold module " << rm.module << ")\n";
    }

    if (!map_path.empty()) {
        std::ifstream mf(map_path);
        if (!mf) { std::cerr << "cannot open " << map_path << "\n"; return 2; }
        std::string line;
        while (std::getline(mf, line)) {
            auto tab = line.find('\t');
            if (tab == std::string::npos) continue;
            gate_to_gold[line.substr(tab + 1)] = line.substr(0, tab);
        }
        std::cout << "name map: " << gate_to_gold.size() << " pairs\n";
    }

    BoolNet net;
    Cones gold(*gold_m, net);
    gold.mark_synthesis_side();

    // The map's gold-side label need not be the name gold's own netlist uses:
    // a net can answer to several names (yosys writes the top-level `led_int`,
    // the placement labels it by the RTL name `core.johnson`).  Resolve each
    // label to the state name gold actually carries, or the two sides end up
    // with different free variables for the same register and every cone
    // "differs".
    {
        // Every name a gold state answers to, mapped to that state.  Built in
        // states() order and keeping the first claimant, which is the answer
        // the scan this replaces would have reached.
        std::map<std::string, std::string> gold_by_name;
        for (const auto &g : gold.states())
            for (const auto &n : gold.synonyms(g)) gold_by_name.emplace(n, g);
        std::map<std::string, std::string> resolved;
        for (const auto &[gate_net, label] : gate_to_gold) {
            // Try the preferred name, then every other name the same net
            // answers to.  A register left unmatched is not one lost cone: it
            // is a different free variable on each side, so everything reading
            // it differs too -- which is how six registers here made a hundred
            // look wrong.
            std::vector<std::string> cands{label};
            auto a = gate_alts.find(gate_net);
            if (a != gate_alts.end())
                for (const auto &n : a->second)
                    if (n != label) cands.push_back(n);
            std::string target = label;
            for (const auto &c : cands) {
                auto hit = gold_by_name.find(c);
                if (hit != gold_by_name.end()) { target = hit->second; break; }
            }
            resolved[gate_net] = target;
        }
        gate_to_gold.swap(resolved);
    }
    // Match by any shared name, not just an identical one.  With --map the
    // gate's states already carry the gold's names, so this is an equality.
    auto match = [&](const Cones &gold_c, const Cones &gate_c) {
        std::vector<std::pair<std::string, std::string>> common;   // (gold, gate)
        // Index the gate side by every name it could be matched on: the label
        // the placement gave it if it has one, else each of its own synonyms.
        // states() is a set, so "the first gate state that matches" is the
        // least one, and taking the minimum over the index says the same thing
        // as the scan it replaces -- without asking every state about every
        // other one, which on a SoC is half a million questions whose answers
        // are all the same handful of names.
        std::map<std::string, std::set<std::string>> gate_by_name;
        for (const auto &t : gate_c.states()) {
            auto mapped = gate_to_gold.find(t);
            if (mapped != gate_to_gold.end())
                gate_by_name[mapped->second].insert(t);
            else
                for (const auto &n : gate_c.synonyms(t)) gate_by_name[n].insert(t);
        }
        for (const auto &g : gold_c.states()) {
            const std::string *best = nullptr;
            for (const auto &n : gold_c.synonyms(g)) {
                auto it = gate_by_name.find(n);
                if (it == gate_by_name.end() || it->second.empty()) continue;
                const std::string &cand = *it->second.begin();
                if (!best || cand < *best) best = &cand;
            }
            if (best) common.emplace_back(g, *best);
        }
        std::sort(common.begin(), common.end());
        return common;
    };
    // --invert: one gold label per line (any name the gold register answers
    // to) whose gate counterpart stores the complement -- a synthesis that
    // folded an inverter into the register against one that kept it.  The
    // gate side then reads the shared symbol negated and reports its next
    // state negated, so the pair is compared in the gold's polarity.
    std::set<std::string> invert_labels;
    if (!invert_p.empty()) {
        std::ifstream inf(invert_p);
        if (!inf) { std::cerr << "cannot open " << invert_p << "\n"; return 2; }
        for (std::string line; std::getline(inf, line);)
            if (!line.empty()) invert_labels.insert(line);
    }
    // the shared symbol is the gold's state name
    auto inverted_of = [&](const Cones &gold_c, const std::vector<std::pair<std::string, std::string>> &common,
                           std::set<std::string> *seen) {
        std::set<std::string> inv;
        for (const auto &[g, t] : common)
            for (const auto &n : gold_c.synonyms(g))
                if (invert_labels.count(n)) { inv.insert(g); if (seen) seen->insert(n); }
        return inv;
    };

    // --pair-memories.  Two syntheses of one RTL need not build a memory from
    // the same primitives (RAM64X1D against RAM32M, one block RAM against
    // another's width), so nothing names which cut is which.  What the two
    // decompositions do share is the boundary: a read bit is the same read bit
    // when its read address, write address, write enable and write data are
    // the same functions of the shared registers and inputs.  So each read
    // symbol gets a key of equivalence classes of those functions (equal
    // literals first, a SAT miter where the structures differ) and equal keys
    // are paired.  A boundary that itself reads a memory only matches once
    // that memory is paired, so this runs in rounds on scratch cones until
    // nothing new pairs; the real cones are then built with the cuts in place.
    std::map<std::string, std::string> dsp_pairs;   // gate DSP instance -> the gold's
    std::map<std::string, std::string> gold_rename;  // gold duplicate register -> the symbol of the pair it duplicates
    std::vector<std::pair<std::string, std::string>> extra_pairs;   // (gold, gate) pairs beyond the name match
    std::map<std::string, bool> gold_consts, gate_consts;            // registers one side keeps that provably never change
    std::set<std::string> not_const;                                 // "g:<name>" / "t:<name>" found not constant: not asked again
    std::set<std::pair<std::string, std::string>> not_same;          // (gold, gate) register pairs the solver refuted
    if (pair_mem) {
        size_t paired_total = 0;
        int rounds = 0;
        size_t gold_unpaired = 0, gate_unpaired = 0;
        for (; rounds < 8; rounds++) {
            BoolNet snet;
            Cones sg(*gold_m, snet, gold_rename);
            sg.mark_synthesis_side();
            sg.set_constants(gold_consts);
            Cones st(*gate_m, snet, gate_to_gold);
            st.set_mem_cuts(mem_cuts);
            st.set_constants(gate_consts);
            st.set_inverted(inverted_of(sg, match(sg, st), nullptr));
            const auto &gp = sg.mem_ports();
            const auto &tp = st.mem_ports();
            std::unique_ptr<Session> ss = make_session(snet, solver);
            std::vector<Lit> reps;   // one representative literal per function seen
            auto cls = [&](Lit l) -> int {
                if (l == LIT_FALSE) return -1;
                if (l == LIT_TRUE) return -2;
                for (size_t i = 0; i < reps.size(); i++) {
                    if (reps[i] == l) return int(i);
                    Lit m = snet.mk_xor(reps[i], l);
                    if (m == LIT_TRUE) continue;
                    if (m == LIT_FALSE || ss->check(m) == Result::Unsat) return int(i);
                }
                reps.push_back(l);
                return int(reps.size()) - 1;
            };
            // A group with one bit per read symbol (write data) is taken at
            // this bit; the rest (addresses, enables) whole.  Trailing
            // constant-zero bits are dropped, so a 64-deep primitive with its
            // top address bit tied low keys the same as a 32-deep one.
            using Key = std::vector<std::pair<std::string, std::vector<int>>>;
            auto key_of = [&](const Cones::MemPort &m, int d, bool nodata = false) {
                Key k;
                for (const auto &g : m.boundary) {
                    std::vector<int> v;
                    // Only a data group goes bit by bit: a one-bit primitive's
                    // write enable is one bit too, but it is the port's, not the bit's.
                    const bool is_data = g.what == "write data" || g.what.rfind("DI", 0) == 0;
                    const bool per_bit = !m.dsp && d >= 0 && is_data && g.bits.size() == m.out_sym.size();
                    if (per_bit && nodata) continue;
                    for (size_t i = 0; i < g.bits.size(); i++) {
                        if (per_bit && int(i) != d) continue;
                        const bool dc = i < g.dontcare.size() && g.dontcare[i];
                        v.push_back(dc ? -3 : cls(g.bits[i]));
                    }
                    while (!v.empty() && v.back() == -1) v.pop_back();
                    if (v.empty()) continue;   // a pin left out and a pin tied low are the same pin
                    k.emplace_back(g.what, std::move(v));
                }
                std::sort(k.begin(), k.end());
                return k;
            };
            std::set<std::string> gold_taken;
            for (const auto &kv : mem_cuts) gold_taken.insert(kv.second);
            std::map<Key, std::vector<std::pair<const Cones::MemPort *, int>>> gold_keys, gate_keys;
            gold_unpaired = gate_unpaired = 0;
            for (const auto &m : gp) {
                if (m.dsp) {
                    bool done = false;
                    for (const auto &kv : dsp_pairs) done |= kv.second == m.where;
                    if (!done) { gold_keys[key_of(m, -1)].emplace_back(&m, -1); gold_unpaired++; }
                } else
                    for (size_t d = 0; d < m.out_sym.size(); d++)
                        if (!gold_taken.count(m.out_sym[d])) { gold_keys[key_of(m, int(d))].emplace_back(&m, int(d)); gold_unpaired++; }
            }
            for (const auto &m : tp) {
                if (m.dsp) {
                    if (!dsp_pairs.count(m.where)) { gate_keys[key_of(m, -1)].emplace_back(&m, -1); gate_unpaired++; }
                } else
                    for (size_t d = 0; d < m.out_sym.size(); d++)
                        if (!mem_cuts.count(m.out_sym[d])) { gate_keys[key_of(m, int(d))].emplace_back(&m, int(d)); gate_unpaired++; }
            }
            if (getenv("LVS_PAIR_DEBUG")) {
                auto dump = [&](const char *side, const std::map<Key, std::vector<std::pair<const Cones::MemPort *, int>>> &keys) {
                    for (const auto &[k, v] : keys) {
                        std::cerr << side << " key";
                        for (const auto &[what, bits] : k) {
                            std::cerr << " | " << what << ":";
                            for (int c : bits) std::cerr << " " << c;
                        }
                        std::cerr << " ->";
                        for (const auto &[m, d] : v) std::cerr << " " << m->where << "#" << d;
                        std::cerr << "\n";
                    }
                };
                dump("gold", gold_keys);
                dump("gate", gate_keys);
            }
            size_t added = 0;
            for (auto &[k, tv] : gate_keys) {
                auto gi = gold_keys.find(k);
                if (gi == gold_keys.end()) continue;
                auto &gv = gi->second;
                for (size_t i = 0; i < tv.size() && i < gv.size(); i++) {
                    const Cones::MemPort *tm = tv[i].first, *gm = gv[i].first;
                    if (tm->dsp) {
                        dsp_pairs[tm->where] = gm->where;
                        // a DSP's reads are cut per output bit, named "<inst>:<pin>[bit]" (Cones::mem_cut_name)
                        for (const auto &p : dsp::kDsp48e1) {
                            if (!p.out) continue;
                            for (int b = 0; b < std::max(p.width, 1); b++)
                                mem_cuts[tm->where + ":" + p.name + "[" + std::to_string(b) + "]"] =
                                    gm->where + ":" + p.name + "[" + std::to_string(b) + "]";
                        }
                    } else {
                        mem_cuts[tm->out_sym[tv[i].second]] = gm->out_sym[gv[i].second];
                    }
                    added++;
                }
            }
            // A DSP whose key matched nothing exactly: the two syntheses drive the same multiplier with a pin or two
            // differing (one sign-extends A to 30 bits, the other to 25), and only the boundary comparison can say
            // whether that matters.  Pair each leftover gate DSP with the leftover gold DSP agreeing on most groups,
            // so the difference is reported pin by pin rather than as two unpaired blocks.
            {
                std::vector<std::pair<Key, const Cones::MemPort *>> gd, td;
                for (const auto &[k, v] : gold_keys) for (const auto &[m, d] : v) if (m->dsp) gd.emplace_back(k, m);
                for (const auto &[k, v] : gate_keys) for (const auto &[m, d] : v) if (m->dsp && !dsp_pairs.count(m->where)) td.emplace_back(k, m);
                std::set<const Cones::MemPort *> used;
                for (const auto &[tk, tm] : td) {
                    const Cones::MemPort *best = nullptr;
                    size_t best_score = 0;
                    for (const auto &[gk, gm] : gd) {
                        if (used.count(gm)) continue;
                        bool taken = false;
                        for (const auto &kv : dsp_pairs) taken |= kv.second == gm->where;
                        if (taken) continue;
                        size_t score = 1;   // any pairing beats none
                        for (const auto &g : gk) for (const auto &t : tk) if (g == t) score++;
                        if (score > best_score) { best_score = score; best = gm; }
                    }
                    if (!best) continue;
                    used.insert(best);
                    dsp_pairs[tm->where] = best->where;
                    for (const auto &p : dsp::kDsp48e1) {
                        if (!p.out) continue;
                        for (int b = 0; b < std::max(p.width, 1); b++)
                            mem_cuts[tm->where + ":" + p.name + "[" + std::to_string(b) + "]"] =
                                best->where + ":" + p.name + "[" + std::to_string(b) + "]";
                    }
                    added++;
                }
            }
            // A memory whose write data reads its own outputs -- a register
            // file, whose writes are ALU results of its reads -- has no bit
            // whose key is free of unpaired symbols, so the exact match above
            // cannot start.  What does tell the bits apart is who reads them:
            // bit 3 of a read port feeds bit 3 of some paired register and bit
            // 4 does not.  So a symbol's signature is the set of paired
            // registers (and output bits) whose cones read it, and a gate
            // symbol pairs with the one gold symbol of the same address/enable
            // key and the same signature.
            // Registers the names did not pair, paired by function.  yosys's
            // memory_dff gives a read port an address register of its own
            // (`$\cpu.cpuregs$rdreg[0]$q`), a copy of decoded_rs1, which the
            // other synthesis has once; nothing but the next-state function
            // says which register it is.  Two registers are the same when
            // their next states agree given that their held values do -- the
            // hypothesis is what lets a register with an enable, which holds
            // its own symbol, be compared at all.  An unpaired register pairs
            // with an unpaired one of the other side, else with a paired one
            // as its duplicate: it then shares that pair's symbol and is proved
            // against the same partner.  Candidates are those reading the same
            // variables (the own symbol aside); the proof is a SAT question.
            {
                auto cm = match(sg, st);
                std::map<std::string, std::string> partner_of_gate, partner_of_gold;
                for (const auto &[g, t] : cm) { partner_of_gate[t] = g; partner_of_gold[g] = t; }
                // A pair matched through a synonym (the gold net answers to
                // the gate's name, but its state symbol is another of its
                // names) must share ONE symbol, so the match is also a rename.
                for (const auto &[g, t] : cm) gate_to_gold.emplace(t, g);
                // A register only one side has, that provably never leaves its
                // power-up value: its next state is that value whenever its
                // current state is (an inductive hold), and INIT is that value.
                // yosys deletes such registers (picorv32's trap state without
                // CATCH_ILLINSN); a synthesis that keeps one leaves a free
                // variable in every cone downstream, and those then differ
                // from the other side's for no reason the design has.
                {
                    std::set<std::string> extra_g, extra_t;
                    for (const auto &p2 : extra_pairs) { extra_g.insert(p2.first); extra_t.insert(p2.second); }
                    auto holds = [&](Cones &c, const std::string &r, const std::string &sym) -> int {
                        const int init = c.init_value(r);
                        if (init < 0) return -1;
                        const Lit next = c.next_state(r);
                        const Lit s2 = snet.input(sym);
                        // next != init while state == init: satisfiable means it can leave
                        const Lit leave = init ? snet.mk_and(negate(next), s2) : snet.mk_and(next, negate(s2));
                        if (leave == LIT_FALSE) return init;
                        if (leave == LIT_TRUE) return -1;
                        return ss->check(leave) == Result::Unsat ? init : -1;
                    };
                    size_t ng = 0, nt = 0;
                    for (const auto &g : sg.states()) {
                        if (partner_of_gold.count(g) || gold_rename.count(g) || extra_g.count(g) || gold_consts.count(g) || not_const.count("g:" + g)) continue;
                        const int v = holds(sg, g, g);
                        if (v >= 0) { gold_consts[g] = v; ng++; }
                        else not_const.insert("g:" + g);
                    }
                    for (const auto &t : st.states()) {
                        if (partner_of_gate.count(t) || extra_t.count(t)) continue;
                        auto m2 = gate_to_gold.find(t);
                        const std::string sym = m2 == gate_to_gold.end() ? t : m2->second;
                        if (gate_consts.count(sym) || not_const.count("t:" + t)) continue;
                        const int v = holds(st, t, sym);
                        if (v >= 0) { gate_consts[sym] = v; nt++; }
                        else not_const.insert("t:" + t);
                        if (v < 0 && getenv("LVS_PAIR_DEBUG")) {
                            std::cerr << "not constant: gate " << t << " (init " << st.init_value(t) << ") next reads:";
                            for (const auto &n : support_of(snet, st.next_state(t))) std::cerr << " " << n;
                            std::cerr << "\n";
                        }
                    }
                    // A PAIRED register both sides hold at the same power-up
                    // value is constant in both designs, and is read as such on
                    // both -- a cone that reads it on one side only would
                    // otherwise differ for a value the register never takes.
                    size_t nb = 0;
                    for (const auto &[g, t] : cm) {
                        if (gold_consts.count(g) || not_const.count("p:" + g)) continue;
                        const int vg = holds(sg, g, g);
                        if (vg < 0) { not_const.insert("p:" + g); continue; }
                        const int vt = holds(st, t, g);
                        if (vt != vg) { not_const.insert("p:" + g); continue; }
                        gold_consts[g] = vg;
                        gate_consts[g] = vg;
                        nb++;
                    }
                    if (ng || nt || nb) {
                        std::cout << "constant registers: " << ng << " gold, " << nt << " gate never leave their power-up value and are read as it";
                        if (nb) std::cout << ", and " << nb << " paired registers constant on both sides";
                        std::cout << "\n";
                        added += ng + nt + nb;
                    }
                }
                struct RegFn { std::string name, sym; Lit next; std::set<std::string> sup; };
                auto fn_of = [&](Cones &c, const std::string &r, const std::string &sym) {
                    RegFn f{r, sym, c.next_state(r), {}};
                    f.sup = support_of(snet, f.next);
                    f.sup.erase(sym);
                    return f;
                };
                std::vector<RegFn> gold_paired, gate_paired, gate_unpaired, gold_unpaired;
                for (const auto &g : sg.states()) {
                    if (gold_rename.count(g) || gold_consts.count(g)) continue;   // a constant is already accounted for
                    RegFn f = fn_of(sg, g, g);
                    (partner_of_gold.count(g) ? gold_paired : gold_unpaired).push_back(std::move(f));
                }
                std::set<std::string> extra_gate;
                for (const auto &p2 : extra_pairs) extra_gate.insert(p2.second);
                for (const auto &t : st.states()) {
                    auto pt = partner_of_gate.find(t);
                    if (pt != partner_of_gate.end()) { gate_paired.push_back(fn_of(st, t, pt->second)); continue; }
                    if (extra_gate.count(t)) continue;   // paired as a duplicate in an earlier round
                    // A gate register the map names but the match left out (two gate registers mapped to one gold
                    // name: the match keeps one) is unpaired too, and reads the mapped symbol.
                    auto m2 = gate_to_gold.find(t);
                    const std::string sym = m2 == gate_to_gold.end() ? t : m2->second;
                    if (gate_consts.count(sym)) continue;   // a constant is already accounted for
                    gate_unpaired.push_back(fn_of(st, t, sym));
                }
                auto same_given = [&](const RegFn &a, const RegFn &b) {
                    if (not_same.count({a.name, b.name})) return false;
                    Lit miter = snet.mk_xor(a.next, b.next);
                    if (miter == LIT_FALSE) return true;
                    if (miter == LIT_TRUE) { not_same.insert({a.name, b.name}); return false; }
                    Lit hyp = negate(snet.mk_xor(snet.input(a.sym), snet.input(b.sym)));
                    const Result r = ss->check(snet.mk_and(miter, hyp));
                    if (r != Result::Unsat) not_same.insert({a.name, b.name});
                    if (getenv("LVS_PAIR_DEBUG") && r == Result::Unsat) {
                        // re-ask with a fresh session: an incremental session answering differently is a bug worth knowing about
                        std::unique_ptr<Session> fresh = make_session(snet, solver);
                        const Result r2 = fresh->check(snet.mk_and(miter, hyp));
                        const Result r3 = fresh->check(miter);
                        std::cerr << "same_given " << a.name << " / " << b.name << ": session " << (r == Result::Unsat ? "unsat" : "sat")
                                  << ", fresh " << (r2 == Result::Unsat ? "unsat" : r2 == Result::Sat ? "sat" : "unknown")
                                  << ", miter alone " << (r3 == Result::Unsat ? "unsat" : r3 == Result::Sat ? "sat" : "unknown") << "\n";
                    }
                    return r == Result::Unsat;
                };
                // The two syntheses' cones for one register need not read
                // exactly the same variables (one keeps a redundant condition
                // the other dropped), so candidates are ranked by how alike
                // their supports are and the best few are put to the solver.
                auto similarity = [](const std::set<std::string> &a, const std::set<std::string> &b) {
                    size_t common = 0;
                    for (const auto &n : a) common += b.count(n);
                    const size_t uni = a.size() + b.size() - common;
                    return uni == 0 ? 1.0 : double(common) / double(uni);
                };
                auto candidates = [&](const RegFn &f, const std::vector<RegFn> &pool, const std::set<std::string> &skip) {
                    std::vector<std::pair<double, const RegFn *>> v;
                    for (const RegFn &c : pool) {
                        if (skip.count(c.name)) continue;
                        const double sim = similarity(f.sup, c.sup);
                        if (sim >= 0.5) v.emplace_back(sim, &c);
                    }
                    std::sort(v.begin(), v.end(), [](const auto &x, const auto &y) { return x.first > y.first; });
                    if (v.size() > 6) v.resize(6);
                    return v;
                };
                if (getenv("LVS_PAIR_DEBUG")) {
                    std::cerr << "register pairing: common " << cm.size() << ", gold paired " << gold_paired.size() << " unpaired "
                              << gold_unpaired.size() << ", gate paired " << gate_paired.size() << " unpaired " << gate_unpaired.size() << "\n";
                }
                size_t by_fn = 0, as_dup = 0;
                std::set<std::string> taken, none;
                for (const RegFn &g : gold_unpaired) {
                    bool done = false;
                    if (getenv("LVS_PAIR_DEBUG")) {
                        std::cerr << "gold unpaired " << g.name << " candidates:";
                        for (const auto &[sim, t] : candidates(g, gate_unpaired, taken)) std::cerr << " U:" << t->name << "@" << sim;
                        for (const auto &[sim, t] : candidates(g, gate_paired, none)) std::cerr << " P:" << t->name << "@" << sim;
                        std::cerr << "\n";
                    }
                    for (const auto &[sim, t] : candidates(g, gate_unpaired, taken)) {
                        if (!same_given(g, *t)) continue;
                        if (t->sym != t->name) {
                            // The gate register already carries a gold symbol (the map named it, and another gate register won
                            // the name match): equal to it, this gold register is a duplicate of THAT gold register, and the
                            // proof is of both against the one symbol -- not a new pairing that would re-home the gate's state.
                            if (getenv("LVS_PAIR_DEBUG")) std::cerr << "gold duplicate: " << g.name << " = " << t->name << " (symbol " << t->sym << ", sim " << sim << ")\n";
                            gold_rename[g.name] = t->sym;
                            extra_pairs.emplace_back(g.name, t->name);
                            as_dup++;
                            done = true;
                            break;
                        }
                        if (getenv("LVS_PAIR_DEBUG")) std::cerr << "pair by function: " << g.name << " = " << t->name << " (sim " << sim << ")\n";
                        gate_to_gold[t->name] = g.name;
                        taken.insert(t->name);
                        by_fn++;
                        done = true;
                        break;
                    }
                    if (done) continue;
                    for (const auto &[sim, t] : candidates(g, gate_paired, none)) {
                        if (!same_given(g, *t)) continue;
                        if (getenv("LVS_PAIR_DEBUG")) std::cerr << "gold duplicate: " << g.name << " = " << t->name << " (symbol " << t->sym << ", sim " << sim << ")\n";
                        gold_rename[g.name] = t->sym;   // the pair's shared symbol, the gold partner's name
                        extra_pairs.emplace_back(g.name, t->name);
                        as_dup++;
                        break;
                    }
                }
                for (const RegFn &t : gate_unpaired) {
                    if (taken.count(t.name)) continue;
                    if (getenv("LVS_PAIR_DEBUG")) {
                        std::cerr << "gate unpaired " << t.name << " (sym " << t.sym << ") candidates:";
                        for (const auto &[sim, g] : candidates(t, gold_paired, none)) std::cerr << " " << g->name << "@" << sim;
                        std::cerr << "\n";
                    }
                    for (const auto &[sim, g] : candidates(t, gold_paired, none)) {
                        if (!same_given(*g, t)) continue;
                        if (getenv("LVS_PAIR_DEBUG")) std::cerr << "gate duplicate: " << g->name << " = " << t.name << " (sim " << sim << ")\n";
                        gate_to_gold[t.name] = g->name;
                        extra_pairs.emplace_back(g->name, t.name);
                        taken.insert(t.name);
                        as_dup++;
                        break;
                    }
                }
                if (by_fn || as_dup) {
                    std::cout << "register pairing: " << by_fn << " unpaired registers paired by next-state function, "
                              << as_dup << " paired as duplicates of an already paired register\n";
                    added += by_fn + as_dup;
                }
            }
            if (!added) {
                std::set<std::string> gold_syms, gate_syms;
                for (const auto &[k, v] : gold_keys) for (const auto &[m, d] : v) if (!m->dsp) gold_syms.insert(m->out_sym[d]);
                for (const auto &[k, v] : gate_keys) for (const auto &[m, d] : v) if (!m->dsp) gate_syms.insert(m->out_sym[d]);
                std::map<std::string, std::set<std::string>> sig;
                auto note = [&](const std::string &who, Lit l) {
                    for (const auto &n : support_of(snet, l))
                        if (gold_syms.count(n) || gate_syms.count(n)) sig[n].insert(who);
                };
                for (const auto &[g, t] : match(sg, st)) { note(g, sg.next_state(g)); note(g, st.next_state(t)); }
                for (const auto &[g, t] : extra_pairs) { note(g, sg.next_state(g)); note(g, st.next_state(t)); }
                auto gate_outs = st.output_bits();
                for (const auto &[port, bit] : sg.output_bits()) {
                    bool has = false;
                    for (const auto &[gp2, gb] : gate_outs) if (gp2 == port && gb == bit) has = true;
                    if (!has) continue;
                    const std::string who = "out:" + port + "[" + std::to_string(bit) + "]";
                    note(who, sg.output_bit(port, bit < 0 ? 0 : bit));
                    note(who, st.output_bit(port, bit < 0 ? 0 : bit));
                }
                using SigKey = std::pair<Key, std::set<std::string>>;
                std::map<SigKey, std::vector<std::pair<const Cones::MemPort *, int>>> gk2, tk2;
                for (const auto &[k, v] : gold_keys)
                    for (const auto &[m, d] : v) {
                        if (m->dsp) continue;
                        auto sg2 = sig.find(m->out_sym[d]);
                        if (sg2 == sig.end()) continue;
                        gk2[{key_of(*m, d, true), sg2->second}].emplace_back(m, d);
                    }
                for (const auto &[k, v] : gate_keys)
                    for (const auto &[m, d] : v) {
                        if (m->dsp) continue;
                        auto sg2 = sig.find(m->out_sym[d]);
                        if (sg2 == sig.end()) continue;
                        tk2[{key_of(*m, d, true), sg2->second}].emplace_back(m, d);
                    }
                if (getenv("LVS_PAIR_DEBUG")) {
                    auto dump = [&](const char *side, const std::map<SigKey, std::vector<std::pair<const Cones::MemPort *, int>>> &keys) {
                        for (const auto &[k, v] : keys) {
                            std::cerr << side << " sig";
                            for (const auto &[what, bits] : k.first) {
                                std::cerr << " | " << what << ":";
                                for (int c : bits) std::cerr << " " << c;
                            }
                            std::cerr << " | readers(" << k.second.size() << "):";
                            size_t i = 0;
                            for (const auto &r : k.second) { if (i++ < 6) std::cerr << " " << r; }
                            std::cerr << " ->";
                            for (const auto &[m, d] : v) std::cerr << " " << m->out_sym[d];
                            std::cerr << "\n";
                        }
                    };
                    dump("gold", gk2);
                    dump("gate", tk2);
                }
                size_t by_sig = 0;
                for (const auto &[k, tv] : tk2) {
                    if (tv.size() != 1) continue;
                    auto gi = gk2.find(k);
                    if (gi == gk2.end() || gi->second.size() != 1) continue;
                    mem_cuts[tv[0].first->out_sym[tv[0].second]] = gi->second[0].first->out_sym[gi->second[0].second];
                    added++;
                    by_sig++;
                }
                if (by_sig) std::cout << "memory pairing: " << by_sig << " read symbols paired by their readers' signature\n";
            }
            paired_total += added;
            gold_unpaired -= added;
            gate_unpaired -= added;
            if (!added) break;
        }
        std::cout << "memory pairing: " << paired_total << " read symbols/DSPs paired by boundary in " << (rounds + 1)
                  << " round(s); " << gold_unpaired << " gold and " << gate_unpaired << " gate left unpaired\n";
    }

    gold.set_rename(gold_rename);
    gold.set_constants(gold_consts);
    {
        // Every name match is a rename too (see the pairing rounds): the two
        // sides of a pair read one symbol, whichever of the gold net's names
        // the gate happened to match on.
        BoolNet tmp;
        Cones g0(*gate_m, tmp, gate_to_gold);
        for (const auto &[g, t] : match(gold, g0)) gate_to_gold.emplace(t, g);
    }
    Cones gate(*gate_m, net, gate_to_gold);
    gate.set_mem_cuts(mem_cuts);
    gate.set_constants(gate_consts);
    std::vector<std::pair<std::string, std::string>> common = match(gold, gate);   // (gold, gate)
    {
        // A gate register the map names but the name match left out (two gate
        // registers mapped to one gold name: the match keeps the first) is a
        // duplicate on the gate side, and is proved against that gold register
        // too, as the extra pairs from the function pairing are.
        std::set<std::string> matched_gate;
        for (const auto &c : common) matched_gate.insert(c.second);
        for (const auto &[t, g] : gate_to_gold)
            if (!matched_gate.count(t) && gate.states().count(t) && gold.states().count(g)) extra_pairs.emplace_back(g, t);
    }
    for (const auto &p : extra_pairs)
        if (std::find(common.begin(), common.end(), p) == common.end()) common.push_back(p);
    std::sort(common.begin(), common.end());

    std::cout << "registers: " << gold.states().size() << " gold, " << gate.states().size()
              << " gate, " << common.size() << " matched by name\n";
    std::set<std::string> inv_gate;   // shared symbols the gate stores complemented
    if (!invert_p.empty()) {
        std::set<std::string> seen;
        inv_gate = inverted_of(gold, common, &seen);
        gate.set_inverted(inv_gate);
        std::cout << "inverted pairs: " << inv_gate.size() << " (gate register holds the complement)";
        size_t unmatched = 0;
        for (const auto &l : invert_labels) if (!seen.count(l)) unmatched++;
        if (unmatched) std::cout << ", " << unmatched << " labels name no matched register";
        std::cout << "\n";
    }
    if (common.size() != gold.states().size() || common.size() != gate.states().size()) {
        // Name them.  A count says something is wrong; the names say what, and
        // an unmatched register poisons every cone downstream of it -- its two
        // sides become different free variables, so anything reading it
        // differs for a reason that has nothing to do with the logic.
        std::set<std::string> gm, tm;
        for (const auto &c : common) { gm.insert(c.first); tm.insert(c.second); }
        auto name_them = [](const char *side, const std::set<std::string> &all,
                            const std::set<std::string> &matched) {
            std::vector<std::string> missing;
            for (const auto &s : all)
                if (!matched.count(s)) missing.push_back(s);
            if (missing.empty()) return;
            std::cout << "  " << missing.size() << " unmatched on the " << side << " side:";
            for (size_t i = 0; i < missing.size() && i < 8; i++) std::cout << " " << missing[i];
            if (missing.size() > 8) std::cout << " ...";
            std::cout << "\n";
        };
        name_them("gold", gold.states(), gm);
        name_them("gate", gate.states(), tm);
        // ...and what the placement thought each unmatched one was called.
        // A count plus two lists says they did not meet; this says where.
        for (const auto &t : gate.states()) {
            if (tm.count(t)) continue;
            auto m = gate_to_gold.find(t);
            std::cout << "    " << t << " -> "
                      << (m == gate_to_gold.end() ? std::string("(no placement label)") : m->second)
                      << "\n";
        }
        std::cout << "  (their cones are not comparable, and neither is anything reading them)\n";
    }
    // One session for the whole run: both designs' cones live in `net`, and a
    // solver told that once can keep what it learns from one register to the
    // next instead of meeting the same network again per question.
    std::unique_ptr<Session> session = make_session(net, solver);
    std::cout << "solver: " << session->describe() << "\n\n";

    int proved = 0, differ = 0, unknown = 0;
    double solver_secs = 0;
    int trivial = 0, asked = 0;
    auto t0 = std::chrono::steady_clock::now();

    // Which named variables a cone actually reads.  A miter that fails says
    // only "these two are not the same function"; the supports say whether the
    // two sides are even looking at the same inputs, which is the difference
    // between a logic error and a correspondence error -- and the second is
    // what nearly every failure here has turned out to be.
    std::map<uint32_t, std::string> input_of;
    auto support = [&](Lit l) {
        if (input_of.size() != net.input_order().size()) {
            input_of.clear();
            for (const auto &n : net.input_order()) input_of[node_of(net.input_lit(n))] = n;
        }
        std::set<std::string> out;
        std::vector<uint32_t> stack{node_of(l)};
        std::set<uint32_t> seen;
        while (!stack.empty()) {
            uint32_t n = stack.back();
            stack.pop_back();
            if (n == 0 || !seen.insert(n).second) continue;
            auto in = input_of.find(n);
            if (in != input_of.end()) { out.insert(in->second); continue; }
            auto a = net.ands().find(n);
            if (a == net.ands().end()) continue;
            stack.push_back(node_of(a->second.a));
            stack.push_back(node_of(a->second.b));
        }
        return out;
    };

    // What every question is asked under: the register-group invariants found
    // below (LIT_TRUE until then).  A miter that is satisfiable only in a state
    // neither design can reach is not a difference between the designs.
    Lit assume = LIT_TRUE;
    // One question's verdict, printed and counted.  Called in question order
    // once the solving is done, which may have happened on several threads.
    auto report = [&](const std::string &label, Lit a, Lit b, Result r) {
        if (r == Result::Unsat) { proved++; if (!quiet) std::cout << "  proved  " << label << "\n"; }
        else if (r == Result::Sat) {
            differ++;
            std::cout << "  DIFFER  " << label << "\n";
            if (explain) {
                std::set<std::string> ga = support(a), gb = support(b);
                std::vector<std::string> only_a, only_b;
                std::set_difference(ga.begin(), ga.end(), gb.begin(), gb.end(),
                                    std::back_inserter(only_a));
                std::set_difference(gb.begin(), gb.end(), ga.begin(), ga.end(),
                                    std::back_inserter(only_b));
                // How many names to print per side.  Six is enough to see the
                // shape of a failure; a bigger number is for reading one
                // failure closely, which is why it is settable.
                size_t explain_cap = 6;
                if (const char *e = getenv("LVS_EXPLAIN_CAP")) explain_cap = size_t(atoi(e));
                auto few = [&](const char *what, const std::vector<std::string> &v) {
                    if (v.empty()) return;
                    std::cout << "            " << what << " (" << v.size() << "):";
                    for (size_t i = 0; i < v.size() && i < explain_cap; i++) std::cout << " " << v[i];
                    if (v.size() > explain_cap) std::cout << " ...";
                    std::cout << "\n";
                };
                // Naming one signal prints what each side reads in full,
                // rather than only the difference.  A difference set says
                // which names are missing; it does not say what the cone that
                // lost them is built from, and that is what you need when the
                // netlist plainly carries a dependency the checker does not.
                if (const char *want = getenv("LVS_SUPPORT_OF")) {
                    if (label.find(want) != std::string::npos) {
                        auto all = [&](const char *side, const std::set<std::string> &g) {
                            std::cout << "            " << side << " reads (" << g.size() << "):";
                            for (const auto &n : g) std::cout << " " << n;
                            std::cout << "\n";
                        };
                        all("gold", ga);
                        all("gate", gb);
                    }
                }
                if (only_a.empty() && only_b.empty())
                    std::cout << "            same " << ga.size()
                              << " inputs on both sides, so the logic itself differs\n";
                few("only the first side reads", only_a);
                few("only the second side reads", only_b);
            }
        }
        else { unknown++; std::cout << "  unknown " << label << "\n"; }
    };

    // A question is queued, not solved on the spot: building its miter
    // extends the shared network (cones are made on demand, and mk_xor hashes
    // into it), which has to be finished before several sessions read the
    // network at once.  flush() then solves the queue in parallel.  The
    // invariants assumed in every question are ANDed in here, while the
    // network is still the main thread's to extend.
    struct Question
    {
        std::string label;
        Lit a, b, miter;
        Result r = Result::Unknown;
        double secs = 0;
    };
    std::vector<Question> pending;
    auto check = [&](const std::string &label, Lit a, Lit b) {
        Lit miter = net.mk_xor(a, b);
        if (!dump_prefix.empty()) {
            // the same question in a form another solver can be handed
            std::string safe = label;
            for (char &c : safe) if (!isalnum((unsigned char)c)) c = '_';
            std::ofstream(dump_prefix + safe + (solver.format == Format::Dimacs ? ".cnf" : ".smt2"))
                << emit(net, miter, solver.format);
        }
        asked++;
        if (assume != LIT_TRUE && miter != 0) miter = net.mk_and(miter, assume);
        // A miter that structural hashing has already folded to the constant 0 is proved (and to the constant 1, refuted): no solver is
        // needed, and on a design whose two sides came from the same netlist that is nearly every question.
        if (miter == 0) {
            trivial++;
            report(label, a, b, Result::Unsat);
            return;
        }
        pending.push_back(Question{label, a, b, miter});
    };
    // The sessions: the first is the one made above, which the pairing and
    // the invariants also ask directly; more are made on the first flush
    // that needs them.  Each is its own solver over the one, by then
    // read-only, network.  An external command is run one at a time.
    std::vector<std::unique_ptr<Session>> extra_sessions;
    const bool linked_solver = solver.command == linked_cadical_name() || solver.command == linked_z3_name();
    auto flush = [&]() {
        if (pending.empty()) return;
        const int n = linked_solver ? std::max(1, std::min<int>(jobs, int(pending.size()))) : 1;
        while (int(extra_sessions.size()) + 1 < n) extra_sessions.push_back(make_session(net, solver));
        std::atomic<size_t> next{0};
        auto worker = [&](Session *s) {
            for (;;) {
                size_t i = next.fetch_add(1);
                if (i >= pending.size()) break;
                Question &q = pending[i];
                auto ts = std::chrono::steady_clock::now();
                q.r = s->check(q.miter);
                q.secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - ts).count();
            }
        };
        std::vector<std::thread> threads;
        for (int t = 1; t < n; t++) threads.emplace_back(worker, extra_sessions[t - 1].get());
        worker(session.get());
        for (auto &t : threads) t.join();
        for (const Question &q : pending) {
            solver_secs += q.secs;
            if (getenv("LVS_PROFILE")) std::cerr << "  [solve " << q.secs << "s] " << q.label << "\n";
            report(q.label, q.a, q.b, q.r);
        }
        pending.clear();
    };

    // Reachable values of small register groups.  Two syntheses of one RTL
    // agree on every reachable state and are free to disagree elsewhere: a
    // `(* parallel_case *)` over a one-hot state register is a licence each
    // tool takes differently for the states that are never one-hot, and the
    // resulting cones differ on exactly those.  So for each register group
    // (bits of one RTL name, up to 8 of them, all paired) the set of values
    // it can take is computed from its power-up value by SAT, on each side,
    // as an inductive invariant: a value is added when either side's next
    // state can reach it from the set.  The union holds in both designs, and
    // is assumed in every question from here on.  A group that can take
    // every value adds nothing and is dropped; one that does not converge
    // within 64 values is left out too.
    if (pair_mem) {
        std::map<std::string, std::vector<std::pair<int, std::pair<std::string, std::string>>>> groups;   // base -> [(bit, (gold, gate))]
        for (const auto &[g, t] : common) {
            auto lb = t.rfind('[');
            if (lb == std::string::npos || t.back() != ']') continue;
            const int bit = atoi(t.substr(lb + 1).c_str());
            groups[t.substr(0, lb)].emplace_back(bit, std::make_pair(g, t));
        }
        int ngroups = 0, nonehot = 0;
        auto t_inv = std::chrono::steady_clock::now();
        for (auto &[base, bits] : groups) {
            if (bits.size() < 2 || bits.size() > 8) continue;
            std::sort(bits.begin(), bits.end());
            const size_t n = bits.size();
            std::vector<Lit> syms, ng, nt;
            uint64_t init = 0;
            bool ok = true;
            for (size_t i = 0; i < n && ok; i++) {
                const auto &[g, t] = bits[i].second;
                const int ig = gold.init_value(g);
                int it = gate.init_value(t);
                if (it >= 0 && inv_gate.count(g)) it = 1 - it;
                if (ig < 0 || it != ig) {
                    if (getenv("LVS_PAIR_DEBUG")) std::cerr << "invariant: " << base << " skipped, bit " << bits[i].first << " init gold " << ig << " gate " << it << "\n";
                    ok = false;
                    break;
                }
                if (ig) init |= uint64_t(1) << i;
                syms.push_back(net.input(g));
                ng.push_back(gold.next_state(g));
                nt.push_back(gate.next_state(t));
            }
            if (!ok) continue;
            auto eq_vec = [&](const std::vector<Lit> &v, uint64_t w) {
                Lit r = LIT_TRUE;
                for (size_t i = 0; i < n; i++) r = net.mk_and(r, ((w >> i) & 1) ? v[i] : negate(v[i]));
                return r;
            };
            std::set<uint64_t> reach{init};
            auto in_set = [&](const std::vector<Lit> &v, bool with_init) {
                Lit r = LIT_FALSE;
                for (uint64_t w : reach) if (with_init || w != init) r = net.mk_or(r, eq_vec(v, w));
                return r;
            };
            // The power-up value is explored on the gold side only.  A state
            // machine powers up at zero -- no state at all under a full_case
            // -- and each tool sends it wherever it likes from there, so
            // exploring both from it reaches everything.  Every other state is
            // explored on both sides.  Whether the gate agrees from power-up
            // is asked at the end, and if it does not, the power-up value is
            // left out of the assumption and said so: the designs then agree
            // once reset, which is what a design with a reset promises.
            // From power-up, only the states BOTH designs enter under the same
            // stimulus: a reset takes both to the reset state; the garbage a
            // full_case lets each tool choose from "no state" is rarely the
            // same garbage, and is nobody's reset state.
            bool gave_up = false;
            {
                const Lit cur = eq_vec(syms, init);
                for (uint64_t w = 0; w < (uint64_t(1) << n); w++) {
                    if (reach.count(w)) continue;
                    Lit q = net.mk_and(cur, net.mk_and(eq_vec(ng, w), eq_vec(nt, w)));
                    if (q != LIT_FALSE && session->check(q) == Result::Sat) {
                        reach.insert(w);
                        if (getenv("LVS_PAIR_DEBUG")) std::cerr << "invariant: " << base << " seed " << std::hex << w << std::dec << "\n";
                    }
                    if (reach.size() > 64) { gave_up = true; break; }
                }
            }
            bool changed = true;
            while (changed && !gave_up) {
                changed = false;
                for (int side = 0; side < 2 && !gave_up; side++) {
                    const std::vector<Lit> &nx = side ? nt : ng;
                    const Lit cur = in_set(syms, false);
                    if (cur == LIT_FALSE) continue;
                    Lit esc = net.mk_and(cur, negate(in_set(nx, true)));
                    if (esc == LIT_FALSE || session->check(esc) == Result::Unsat) continue;
                    for (uint64_t w = 0; w < (uint64_t(1) << n); w++) {
                        if (reach.count(w)) continue;
                        Lit q = net.mk_and(cur, eq_vec(nx, w));
                        if (q != LIT_FALSE && session->check(q) == Result::Sat) {
                            reach.insert(w);
                            changed = true;
                            if (getenv("LVS_PAIR_DEBUG") && reach.size() <= 24)
                                std::cerr << "invariant: " << base << " " << (side ? "gate" : "gold") << " reaches " << std::hex << w << std::dec << "\n";
                        }
                        if (reach.size() > 64) { gave_up = true; break; }
                    }
                }
            }
            if (gave_up || reach.size() == (uint64_t(1) << n)) {
                if (getenv("LVS_PAIR_DEBUG")) std::cerr << "invariant: " << base << " (" << n << " bits) " << (gave_up ? "did not converge" : "takes every value") << "\n";
                continue;
            }
            bool with_init = true;
            for (const auto *nx : {&ng, &nt}) {
                Lit esc = net.mk_and(eq_vec(syms, init), negate(in_set(*nx, true)));
                if (esc != LIT_FALSE && session->check(esc) != Result::Unsat) with_init = false;
            }
            bool onehot = true;
            for (uint64_t w : reach) onehot &= __builtin_popcountll(w) == 1;
            if (onehot) nonehot++;
            ngroups++;
            assume = net.mk_and(assume, in_set(syms, with_init));
            if (!quiet || ngroups <= 12)
                std::cout << "invariant: " << base << " (" << n << " bits) takes " << reach.size() << " of " << (1u << n) << " values"
                          << (onehot ? ", all one-hot" : "")
                          << (with_init ? "" : "; from its power-up value a design leaves the set, so that value is not assumed: the designs agree once reset")
                          << "\n";
        }
        if (ngroups)
            std::cout << "invariants: " << ngroups << " register groups confined to their reachable values (" << nonehot << " one-hot), assumed in every question ("
                      << std::chrono::duration<double>(std::chrono::steady_clock::now() - t_inv).count() << "s)\n";
    }

    for (const auto &[gn, tn] : compare)
        check(gn + " vs " + tn, gold.value_of(gn), gate.value_of(tn));
    if (!compare.empty() && common.empty()) {
        flush();
        auto secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
        std::cout << "\n" << proved << " proved, " << differ << " differ, " << unknown
                  << " unknown   (" << secs << "s)\n";
        return differ == 0 && unknown == 0 ? 0 : 1;
    }

    for (const auto &[g, t] : common) {
        if (!only.empty() && g.find(only) == std::string::npos) continue;
        check(g == t ? g : (g + " = " + t), gold.next_state(g), gate.next_state(t));
    }
    // Clock polarity of every matched register: configuration, like a RAM's width.  The proof itself has no edges, so the edge a register
    // captures on is held against the bitstream here.  (Which clock net drives it is a separate question -- clocks are assumed common.)
    {
        int pol_rows = 0, pol_diff = 0, never_clocked = 0;
        for (const auto &[g, t] : common) {
            int gp = gold.clock_inverted(g), tp = gate.clock_inverted(t);
            if (gp < 0 || tp < 0) continue;
            // a clock tied to a constant never ticks, so its edge is nobody's
            // business: the placer may fold any inversion into the slice
            if (gold.clock_is_constant(g)) { never_clocked++; continue; }
            pol_rows++;
            if (gp == tp) continue;
            pol_diff++;
            differ++;
            if (pol_diff <= 40)
                std::cout << "  DIFFER  " << (g == t ? g : g + " = " + t) << " clock edge: gold "
                          << (gp ? "falling" : "rising") << ", gate " << (tp ? "falling" : "rising") << "\n";
        }
        std::cout << "register clock edge: " << pol_rows << " compared, " << pol_diff << " differ";
        if (never_clocked) std::cout << " (" << never_clocked << " with a constant clock, not compared)";
        std::cout << "\n";
    }
    // Which BUFG clocks each matched register.  The extraction traces it only under --routed-clock; without that every register reads as not
    // traced and the row is skipped.  A synthesis register driven by something other than a BUFG (a clock straight from a pad or a BUFR) has no
    // BUFG to compare, so it is counted but not held against the extraction.
    {
        int src_rows = 0, src_diff = 0, untraced = 0, no_bufg = 0;
        std::vector<std::pair<std::string, std::string>> untraced_regs;   // registers whose clock the extraction could not trace
        for (const auto &[g, t] : common) {
            if (gold.clock_inverted(g) < 0 || gate.clock_inverted(t) < 0) continue;
            std::string gc = gold.clock_source(g), tc = gate.clock_source(t);
            if (gc.empty()) { no_bufg++; continue; }
            if (tc.empty()) { untraced++; untraced_regs.emplace_back(g, t); continue; }
            auto site = bufg_site.find(gc);
            std::string gs = site == bufg_site.end() ? gc : site->second;
            src_rows++;
            if (gs == tc) continue;
            // Two syntheses name their clock buffers differently, and the name says nothing: what the buffer is fed from
            // does.  Walk each BUFG's input back through the input buffers to the net, and compare the nets as functions
            // over the shared symbols -- a clock port is the same symbol on both sides.
            if (gate_is_json) {
                auto clock_root = [](const Module &m, std::string cell) {
                    std::string net;
                    for (int hop = 0; hop < 8; hop++) {
                        const Instance *inst = nullptr;
                        for (const auto &i : m.instances) if (i.name == cell) { inst = &i; break; }
                        if (!inst) break;
                        const Pin *p = inst->find_pin("I");
                        if (!p || p->conn.kind != Expr::Kind::Id) break;
                        net = p->conn.name;
                        const Instance *drv = nullptr;
                        for (const auto &i : m.instances) {
                            const Pin *o = i.find_pin("O");
                            if (o && o->conn.kind == Expr::Kind::Id && o->conn.name == net) { drv = &i; break; }
                        }
                        if (!drv || !(drv->type == "IBUF" || drv->type == "IBUFDS" || drv->type.rfind("BUFG", 0) == 0)) break;
                        cell = drv->name;
                    }
                    return net;
                };
                const std::string gr = clock_root(*gold_m, gc), tr = clock_root(*gate_m, tc);
                if (!gr.empty() && !tr.empty() && gold.value_of(gr) == gate.value_of(tr)) continue;
                gs = gc + " <- " + gr;
                tc = tc + " <- " + tr;
            }
            src_diff++;
            differ++;
            if (src_diff <= 40)
                std::cout << "  DIFFER  " << (g == t ? g : g + " = " + t) << " clock source: gold " << gc << " (" << gs << "), gate " << tc << "\n";
        }
        // With the clock tree traced for most registers, one it could not trace is not "unknown": its clock pin reaches no BUFG, which is either
        // a missing pip or a clock the design does not have.  Without --routed-clock nothing is traced and the row is not applicable.
        if (src_rows > 0 && !untraced_regs.empty()) {
            for (size_t i = 0; i < untraced_regs.size(); i++) {
                differ++;
                src_diff++;
                if (i < 40)
                    std::cout << "  DIFFER  " << untraced_regs[i].first << " = " << untraced_regs[i].second
                              << " clock source: gold has a BUFG, the extraction's clock reaches none\n";
            }
            untraced = 0;
        }
        std::cout << "register clock source: " << src_rows << " compared, " << src_diff << " differ (" << untraced
                  << " not traced in the extraction, " << no_bufg << " not driven by a BUFG in the synthesis)\n";
    }
    // What feeds each BUFG.  The extraction (with --routed-clock) writes "// lvs-bufg-src <site> <tile> <pin>" after tracing every BUFGCTRL input
    // back through the clock tree to an MMCM/PLL output, a transceiver clock or a slice; the synthesis side is the cell driving the BUFG's input,
    // placed.  A buffer in the synthesis that the extraction did not trace, or one the extraction has that the synthesis lacks, is a difference.
    {
        std::map<std::string, std::string> gate_src;
        std::vector<std::pair<std::string, std::string>> pad_fabric;   // BUFGs fed from a pad through general routing
        std::ifstream gf(gate_path);
        for (std::string line; std::getline(gf, line);) {
            if (line.rfind("// lvs-bufg-src ", 0) != 0) continue;
            std::istringstream is(line.substr(16));
            std::string site, tile, pin, route;
            is >> site >> tile >> pin >> route;
            gate_src[site] = tile + " " + pin;
            if (route == "fabric" && (tile.rfind("LIOB", 0) == 0 || tile.rfind("RIOB", 0) == 0)) pad_fabric.emplace_back(site, tile);
        }
        if (!gate_src.empty() && !bufg_src.empty()) {
            int rows = 0, bdiff = 0;
            for (const auto &[site, want] : bufg_src) {
                rows++;
                auto it = gate_src.find(site);
                if (it != gate_src.end() && it->second == want) continue;
                bdiff++;
                differ++;
                std::cout << "  DIFFER  " << site << " input: gold " << want << ", gate " << (it == gate_src.end() ? "not traced" : it->second) << "\n";
            }
            for (const auto &[site, got] : gate_src)
                if (!bufg_src.count(site)) {
                    bdiff++;
                    differ++;
                    std::cout << "  DIFFER  " << site << " input: gate " << got << ", no such buffer in the synthesis\n";
                }
            std::cout << "BUFG input source: " << rows << " compared, " << bdiff << " differ\n";
            // Not a difference -- the synthesis cannot say which route is taken -- but a clock pad reaching a BUFG through the fabric is the
            // case Vivado's PLCK-23 rejects: the dedicated clock path from a clock-capable pad is not used.
            for (const auto &[site, tile] : pad_fabric)
                std::cout << "  NOTE    " << site << " input comes from the pad at " << tile
                          << " through general routing, not the dedicated clock path\n";
        }
    }
    auto gate_outs = gate.output_bits();
    for (const auto &[port, bit] : gold.output_bits()) {
        // The two sides need not agree on bus-ness: gold declares an 8-bit
        // `led`, while the fabric names each pad separately from the XDC and so
        // declares scalars called `led[0]`..`led[7]`.  Accept either shape.
        std::string scalar = bit < 0 ? port : port + "[" + std::to_string(bit) + "]";
        bool gate_has = false;
        for (const auto &[gp, gb] : gate_outs)
            if ((gp == port && gb == bit) || (gp == scalar && gb < 0)) { gate_has = true; break; }
        if (!gate_has) {
            std::cout << "  skipped " << port << " -- the gate has no such port"
                      << " (map its pin from the XDC to compare it)\n";
            continue;
        }
        std::string label = bit < 0 ? port : port + "[" + std::to_string(bit) + "]";
        check(label, gold.output_bit(port, bit < 0 ? 0 : bit), gate.output_bit(port, bit < 0 ? 0 : bit));
    }

    // The memories.  Their contents were cut, so what is left to prove is the
    // boundary: read address, write address, write data, write enable.  Prove
    // those equal and the contents are equal by construction -- which is both
    // why the cut is sound and what checks the pairing that made it.
    // Run whenever either side has a cut primitive: a design with DSPs and no block RAM has an empty memory map and used to skip all of this,
    // so its DSPs' boundary and configuration were never looked at.
    if (!mem_cuts.empty() || !gold.mem_ports().empty() || !gate.mem_ports().empty()) {
        const auto &gp = gold.mem_ports();
        const auto &tp = gate.mem_ports();
        // A DSP has no read symbols to pair by.  The placement says which extracted instance each synthesis DSP became (the same map the
        // hard-block check below uses), so pair through that.
        std::map<std::string, const Cones::MemPort *> gold_by_where;
        for (const auto &m : gp)
            if (m.dsp) gold_by_where[m.where] = &m;
        // Pair by the symbol a memory's first read produces: the placement
        // already renamed the gate's to the gold's, so equal symbols are the
        // paired memories, whatever either side calls anything else.
        // ...by every read symbol, not only the first: paired by boundary
        // (--pair-memories) a two-bit RAM32M port meets two one-bit RAM64X1Ds,
        // one per data bit, and the second bit's symbol is nobody's first.
        std::map<std::string, std::pair<const Cones::MemPort *, int>> by_sym;
        for (const auto &m : gp)
            for (size_t d = 0; d < m.out_sym.size(); d++) by_sym.emplace(m.out_sym[d], std::make_pair(&m, int(d)));
        int mem_pairs = 0, mem_unpaired = 0, mem_rows = 0, mem_content_diff = 0, same_page = 0;
        int dsp_paired = 0, patdet_set = 0, patdet_unseen = 0;      // for the one parameter the bitstream has no bit for (below)
        std::set<const Cones::MemPort *> paired_gold;
        // Which bits of a gate port pair with which bits of a gold port.  Empty
        // for a primitive paired whole (a DSP, a placement-paired memory), in
        // which case every boundary group is compared bit for bit as before.
        using BitPairs = std::vector<std::pair<int, int>>;   // (gate bit, gold bit)
        auto compare_pair = [&](const Cones::MemPort &t, const Cones::MemPort &G, const BitPairs &bitpairs) {
            paired_gold.insert(&G);
            mem_pairs++;
            // The two sides list their boundary groups independently, so they
            // are paired by name.  A group only one side has is not silently
            // dropped: it is counted, because a boundary that is checked in
            // part is not a boundary that justifies a cut.
            std::map<std::string, const Cones::MemPort::Group *> gold_grp;
            for (const auto &g2 : G.boundary) gold_grp[g2.what] = &g2;
            // An address bit each side ties to a constant, the same one for
            // reading as for writing, only chooses which part of the RAM a
            // smaller memory uses: an 8-deep FIFO in a 64-entry column is
            // A3..A5 tied low by the synthesis and high by nextpnr's packer,
            // and either way every read finds what the last write left.  Such
            // a bit is not compared, in either address.
            std::set<size_t> page_bits;
            {
                auto grp = [](const Cones::MemPort &p, const char *w) -> const Cones::MemPort::Group * {
                    for (const auto &g2 : p.boundary)
                        if (g2.what == w) return &g2;
                    return nullptr;
                };
                const auto *gr = grp(G, "read address"), *gw = grp(G, "write address");
                const auto *tr = grp(t, "read address"), *tw = grp(t, "write address");
                auto fixed = [](Lit r, Lit w) { return (r == LIT_TRUE || r == LIT_FALSE) && r == w; };
                if (gr && gw && tr && tw)
                    for (size_t i = 0; i < std::min({gr->bits.size(), gw->bits.size(), tr->bits.size(), tw->bits.size()}); i++)
                        if (fixed(gr->bits[i], gw->bits[i]) && fixed(tr->bits[i], tw->bits[i])) page_bits.insert(i);
                same_page += int(page_bits.size());
            }
            // A multiplier is commutative, and a synthesis may feed the RTL's
            // left operand to the DSP's B port.  When the A and B boundaries
            // match the other way round better than straight, the ports are
            // compared swapped (A with B, CEA with CEB, AREG with BREG), and
            // said so.  Only between two syntheses: a bitstream is held to
            // the synthesis that placed it.
            bool swap_ab = false;
            if (G.dsp && pair_mem) {
                auto grp = [](const Cones::MemPort &p, const char *w) -> const Cones::MemPort::Group * {
                    for (const auto &g2 : p.boundary)
                        if (g2.what == w) return &g2;
                    return nullptr;
                };
                auto differs = [&](const Cones::MemPort::Group *a, const Cones::MemPort::Group *b) {
                    size_t d = 0;
                    const size_t n = std::max(a->bits.size(), b->bits.size());
                    for (size_t i = 0; i < n; i++) {
                        if (i < a->dontcare.size() && a->dontcare[i]) continue;
                        if (i < b->dontcare.size() && b->dontcare[i]) continue;
                        // a narrower port is read as extended by its top bit
                        const Lit x = i < a->bits.size() ? a->bits[i] : a->bits.empty() ? LIT_FALSE : a->bits.back();
                        const Lit y = i < b->bits.size() ? b->bits[i] : b->bits.empty() ? LIT_FALSE : b->bits.back();
                        Lit m = net.mk_xor(x, y);
                        if (m == LIT_FALSE) continue;
                        if (m == LIT_TRUE || session->check(assume == LIT_TRUE ? m : net.mk_and(m, assume)) != Result::Unsat) d++;
                    }
                    return d;
                };
                const auto *gA = grp(G, "A"), *gB = grp(G, "B"), *tA = grp(t, "A"), *tB = grp(t, "B");
                if (gA && gB && tA && tB) {
                    const size_t straight = differs(gA, tA) + differs(gB, tB);
                    if (straight && differs(gA, tB) + differs(gB, tA) < straight) {
                        swap_ab = true;
                        std::cout << "  NOTE    " << t.where << ": multiplier operands swapped against " << G.where << " (A is B), compared that way\n";
                    }
                }
            }
            // A DSP's A[29:25] reach only the A:B concatenation (OPMODE X = 11), the pre-adder's D path and ACOUT.  A multiplier that uses
            // none of them (X constant and not 11, no D port, ACOUT unconnected on both sides) does not see those bits, and one synthesis
            // sign-extends its 25-bit operand into them while another leaves them low.  Not a difference in what the block computes.
            bool a_hi_unused = false;
            if (G.dsp && pair_mem) {
                auto grp = [](const Cones::MemPort &p, const char *w) -> const Cones::MemPort::Group * {
                    for (const auto &g2 : p.boundary)
                        if (g2.what == w) return &g2;
                    return nullptr;
                };
                // whether anything reads what the pin drives: a synthesis writes a net on every output pin, read or not
                auto pin_read = [](const Module &m, const std::string &inst, const char *pin) {
                    std::set<std::string> nets;
                    auto names_of = [&](const Expr &e, std::set<std::string> &out) {
                        if (e.kind == Expr::Kind::Id) out.insert(e.name);
                        else if (e.kind == Expr::Kind::BitSel) out.insert(e.name + "[" + std::to_string(e.index) + "]");
                        else if (e.kind == Expr::Kind::Concat)
                            for (const auto &part : e.parts) {
                                if (part.kind == Expr::Kind::Id) out.insert(part.name);
                                else if (part.kind == Expr::Kind::BitSel) out.insert(part.name + "[" + std::to_string(part.index) + "]");
                            }
                    };
                    for (const auto &i : m.instances)
                        if (i.name == inst)
                            if (const Pin *p = i.find_pin(pin)) names_of(p->conn, nets);
                    if (nets.empty()) return false;
                    std::set<std::string> read;
                    for (const auto &i : m.instances) {
                        if (i.name == inst) continue;
                        for (const auto &p : i.pins) names_of(p.conn, read);
                    }
                    for (const auto &a : m.assigns) names_of(a.rhs, read);
                    for (const auto &pd : m.ports)
                        if (pd.dir != PortDecl::Dir::Input) {
                            read.insert(pd.name);
                            for (int b = 0; b < pd.range.width(); b++) read.insert(pd.name + "[" + std::to_string(std::min(pd.range.msb, pd.range.lsb) + b) + "]");
                        }
                    for (const auto &n : nets) if (read.count(n)) return true;
                    return false;
                };
                auto x_not_ab = [&](const Cones::MemPort &p) {
                    const auto *op = grp(p, "OPMODE");
                    if (!op || op->bits.size() < 2) return false;
                    const Lit x0 = op->bits[0], x1 = op->bits[1];
                    const bool c0 = x0 == LIT_TRUE || x0 == LIT_FALSE, c1 = x1 == LIT_TRUE || x1 == LIT_FALSE;
                    return c0 && c1 && !(x0 == LIT_TRUE && x1 == LIT_TRUE);
                };
                auto no_dport = [&](const std::map<std::string, std::string> &c) {
                    auto it = c.find("USE_DPORT");
                    return it == c.end() || it->second == "false";
                };
                a_hi_unused = x_not_ab(G) && x_not_ab(t) && no_dport(G.contents) && no_dport(t.contents) &&
                              !pin_read(*gold_m, G.where, "ACOUT") && !pin_read(*gate_m, t.where, "ACOUT");
                if (getenv("LVS_PAIR_DEBUG"))
                    std::cerr << "dsp " << t.where << ": X not A:B " << x_not_ab(G) << x_not_ab(t) << ", no D " << no_dport(G.contents) << no_dport(t.contents)
                              << ", ACOUT read " << pin_read(*gold_m, G.where, "ACOUT") << pin_read(*gate_m, t.where, "ACOUT") << "\n";
            }
            static const std::map<std::string, std::string> kSwapPin = {{"A", "B"}, {"B", "A"}, {"CEA1", "CEB1"}, {"CEB1", "CEA1"},
                                                                       {"CEA2", "CEB2"}, {"CEB2", "CEA2"}, {"RSTA", "RSTB"}, {"RSTB", "RSTA"},
                                                                       {"ACIN", "BCIN"}, {"BCIN", "ACIN"}};
            static const std::map<std::string, std::string> kSwapRow = {{"AREG", "BREG"}, {"BREG", "AREG"}, {"ACASCREG", "BCASCREG"},
                                                                       {"BCASCREG", "ACASCREG"}, {"A_INPUT", "B_INPUT"}, {"B_INPUT", "A_INPUT"}};
            auto gold_name_of = [&](const std::string &w) {
                if (!swap_ab) return w;
                auto it = kSwapPin.find(w);
                return it == kSwapPin.end() ? w : it->second;
            };
            for (const auto &tg : t.boundary) {
                auto gg = gold_grp.find(gold_name_of(tg.what));
                if (gg == gold_grp.end()) { mem_unpaired++; continue; }
                const auto &gb = *gg->second;
                // A group with one bit per read symbol on both sides (write
                // data) is compared at the paired bits only: the gate's bit 0
                // against whichever gold bit it was paired with.
                const bool per_bit = !bitpairs.empty() && tg.bits.size() == t.out_sym.size() &&
                                     gb.bits.size() == G.out_sym.size() &&
                                     (tg.what == "write data" || tg.what.rfind("DI", 0) == 0);
                if (per_bit) {
                    for (const auto &[td, gd] : bitpairs) {
                        if (size_t(gd) < gb.dontcare.size() && gb.dontcare[gd]) continue;
                        if (size_t(td) < tg.dontcare.size() && tg.dontcare[td]) continue;
                        check(t.where + " " + tg.what + "[" + std::to_string(td) + "]",
                              size_t(gd) < gb.bits.size() ? gb.bits[gd] : LIT_FALSE,
                              size_t(td) < tg.bits.size() ? tg.bits[td] : LIT_FALSE);
                    }
                    gold_grp.erase(gg);
                    continue;
                }
                size_t n = std::max(tg.bits.size(), gb.bits.size());
                // swapped operands differ in width (A is 30 bits, B 18): the narrower is read as extended by its top bit
                const bool swapped_here = swap_ab && (tg.what == "A" || tg.what == "B");
                for (size_t i = 0; i < n; i++) {
                    // The synthesis's don't-cares win: the fabric always has
                    // something on a pin, and a pin the design never wired up
                    // is not a claim about the circuit.
                    if (i < gb.dontcare.size() && gb.dontcare[i]) continue;
                    if (i < tg.dontcare.size() && tg.dontcare[i]) continue;
                    if ((tg.what == "read address" || tg.what == "write address") && page_bits.count(i)) continue;
                    if (a_hi_unused && i >= 25 && (tg.what == "A" || gg->first == "A")) continue;
                    const Lit gl = i < gb.bits.size() ? gb.bits[i] : swapped_here && !gb.bits.empty() ? gb.bits.back() : LIT_FALSE;
                    const Lit tl = i < tg.bits.size() ? tg.bits[i] : swapped_here && !tg.bits.empty() ? tg.bits.back() : LIT_FALSE;
                    check(t.where + " " + tg.what + "[" + std::to_string(i) + "]", gl, tl);
                }
                gold_grp.erase(gg);
            }
            mem_unpaired += int(gold_grp.size());

            // What the cut hides: the contents AND the configuration -- a
            // memory's widths and write modes, a DSP's inversion masks and
            // register enables.  Compared directly, because a boundary that
            // agrees says nothing about what the primitive does with it.
            // A parameter a side leaves out means the primitive's default, which is not always zero (a DSP's AREG is 1), so each side's value
            // for a row is what it says or else the default.  Canonical spelling, as in cone.cpp's cut_config.
            static const std::map<std::string, std::string> kDspDefault = {
                {"A_INPUT", "direct"}, {"B_INPUT", "direct"}, {"AREG", "1"}, {"ACASCREG", "1"}, {"BREG", "1"}, {"BCASCREG", "1"},
                {"ADREG", "1"}, {"ALUMODEREG", "1"}, {"CARRYINREG", "1"}, {"CARRYINSELREG", "1"}, {"CREG", "1"}, {"DREG", "1"},
                {"INMODEREG", "1"}, {"MREG", "1"}, {"OPMODEREG", "1"}, {"PREG", "1"}, {"USE_DPORT", "false"}, {"USE_MULT", "multiply"},
                {"USE_SIMD", "one48"}, {"AUTORESET_PATDET", "noreset"}, {"SEL_MASK", "mask"}, {"SEL_PATTERN", "pattern"},
                {"USE_PATTERN_DETECT", "nopatdet"}, {"MASK", "3fffffffffff"}};
            static const std::map<std::string, std::string> kRamDefault = {
                {"RAM_MODE", "tdp"}, {"WRITE_MODE_A", "writefirst"}, {"WRITE_MODE_B", "writefirst"},
                {"RAM_EXTENSION_A", "none"}, {"RAM_EXTENSION_B", "none"}, {"EN_ECC_READ", "false"}, {"EN_ECC_WRITE", "false"},
                {"RDADDR_COLLISION_HWCONFIG", "delayedwrite"}, {"RSTREG_PRIORITY_A", "rstreg"}, {"RSTREG_PRIORITY_B", "rstreg"}};
            const auto &dflt = G.dsp ? kDspDefault : kRamDefault;
            auto value_of = [&](const std::map<std::string, std::string> &m, const std::string &row) {
                auto it = m.find(row);
                if (it != m.end()) return it->second;
                auto d = dflt.find(row);
                return d == dflt.end() ? std::string("0") : d->second;
            };
            if (G.dsp) {
                dsp_paired++;
                if (value_of(G.contents, "USE_PATTERN_DETECT") != "nopatdet") patdet_set++;
            }
            std::map<std::string, std::string> t_contents = t.contents;
            if (swap_ab) {
                t_contents.clear();
                for (const auto &kv : t.contents) {
                    auto it = kSwapRow.find(kv.first);
                    t_contents[it == kSwapRow.end() ? kv.first : it->second] = kv.second;
                }
            }
            std::set<std::string> rows;
            for (const auto &kv : G.contents) rows.insert(kv.first);
            for (const auto &kv : t_contents) rows.insert(kv.first);
            for (const auto &r : rows) {
                // Not observable: a DSP's USE_PATTERN_DETECT has no bit in the bitstream (PATDET and NO_PATDET give identical bits; database
                // FIXES.md), so there is nothing on the extraction side to hold the synthesis against.  Counted and reported below, not skipped
                // quietly.
                if (G.dsp && r == "USE_PATTERN_DETECT") continue;
                // The pattern detector's own configuration decides nothing a design that neither enables it nor reads its outputs can see:
                // MASK, PATTERN and the rest only shape PATTERNDETECT/PATTERNBDETECT/OVERFLOW/UNDERFLOW.  A nextpnr that writes the default MASK
                // (all ones) and one that leaves it out (all zeros in the bitstream) both build the same multiplier.  Not skipped when the
                // synthesis enables the detector or connects one of those outputs.
                if (G.dsp && !G.patdet_used && value_of(G.contents, "USE_PATTERN_DETECT") == "nopatdet" &&
                    (r == "MASK" || r == "PATTERN" || r == "SEL_MASK" || r == "SEL_PATTERN" || r == "AUTORESET_PATDET")) {
                    patdet_unseen++;
                    continue;
                }
                std::string gv = value_of(G.contents, r);
                std::string tv = value_of(t_contents, r);
                // A row the synthesis left undefined -- yosys writes the
                // unused parity rows as x -- says nothing about what the
                // memory should hold, exactly as a don't-care pin does at the
                // boundary.  The fabric always has some value there.
                if (gv.find('x') != std::string::npos) continue;
                // A port the synthesis does not have (width 0) has no width to compare: the bitstream still writes that port's
                // width marker, at whatever the memory's width makes it, and that is not a claim about the design either.
                if (gv == "0" && (r.rfind("READ_WIDTH_", 0) == 0 || r.rfind("WRITE_WIDTH_", 0) == 0)) continue;
                // A clock's polarity is only meaningful for a port the synthesis uses; the tag of an unused port is whatever the placer left.
                if (!G.dsp && (r == "IS_CLKARDCLK_INVERTED" || r == "IS_CLKBWRCLK_INVERTED")) {
                    const char ab = r == "IS_CLKARDCLK_INVERTED" ? 'A' : 'B';
                    if (value_of(G.contents, std::string("READ_WIDTH_") + ab) == "0" &&
                        value_of(G.contents, std::string("WRITE_WIDTH_") + ab) == "0")
                        continue;
                }
                mem_rows++;
                if (gv == tv) continue;
                mem_content_diff++;
                if (mem_content_diff <= 40)
                    std::cout << "  DIFFER  " << t.where << " " << r << ": gold " << gv
                              << ", gate " << tv << "\n";
            }
        };
        for (const auto &t : tp) {
            if (t.dsp) {
                const Cones::MemPort *gptr = nullptr;
                auto dp = dsp_pairs.find(t.where);
                if (dp != dsp_pairs.end()) {
                    auto it = gold_by_where.find(dp->second);
                    if (it != gold_by_where.end()) gptr = it->second;
                }
                for (const auto &[cell, hb] : hard_blocks) {
                    if (hb.gate_name != t.where && (hb.gate_name_alt.empty() || hb.gate_name_alt != t.where)) continue;
                    auto it = gold_by_where.find(cell);
                    if (it != gold_by_where.end()) gptr = it->second;
                    break;
                }
                if (gptr) compare_pair(t, *gptr, {});
                continue;
            }
            // Group the gate port's read symbols by the gold port they were
            // paired to.  From a placement every symbol of a port goes to one
            // gold port; from a boundary pairing they may go to several.
            std::map<const Cones::MemPort *, BitPairs> by_gold;
            for (size_t d = 0; d < t.out_sym.size(); d++) {
                auto want = mem_cuts.find(t.out_sym[d]);
                if (want == mem_cuts.end()) { if (getenv("LVS_PAIR_DEBUG")) std::cerr << "final: no cut for " << t.out_sym[d] << "\n"; continue; }
                auto g = by_sym.find(want->second);
                if (g == by_sym.end()) { if (getenv("LVS_PAIR_DEBUG")) std::cerr << "final: cut " << t.out_sym[d] << " -> " << want->second << " names no gold read symbol\n"; continue; }
                by_gold[g->second.first].emplace_back(int(d), g->second.second);
            }
            for (const auto &[gp2, bp] : by_gold) compare_pair(t, *gp2, pair_mem ? bp : BitPairs{});
        }
        std::cout << "memories: " << gp.size() << " gold, " << tp.size() << " gate, "
                  << mem_pairs << " paired, " << mem_rows << " content rows compared";
        if (same_page) std::cout << " (" << same_page << " address bits tied to the same constant for read and write, not compared)";
        std::cout << "\n";
        {
            // A cut primitive of the synthesis with no counterpart in the extraction was never compared -- not its boundary, not its
            // configuration -- and passing it silently is how a DSP went unchecked for as long as this tool has existed.  It is unproved.
            int unpaired = 0;
            for (const auto &m : gp)
                if (!paired_gold.count(&m)) unpaired++;
            if (unpaired) {
                std::cout << "  " << unpaired << " of " << gp.size()
                          << " cut primitive(s) of the synthesis have no counterpart in the extraction, so their boundary and configuration were"
                             " not compared (counted as unproved)\n";
                unknown += unpaired;
            }
        }
        if (dsp_paired)
            std::cout << "not observable in the bitstream, so not compared: USE_PATTERN_DETECT (" << patdet_set << " of " << dsp_paired
                      << " DSPs set it to PATDET)\n";
        if (patdet_unseen)
            std::cout << "pattern-detector configuration (MASK, PATTERN, SEL_MASK, SEL_PATTERN, AUTORESET_PATDET) not compared on DSPs that neither enable the "
                         "detector nor use its outputs: " << patdet_unseen << " rows\n";
        if (mem_content_diff)
            std::cout << "cut primitives: " << mem_content_diff
                      << " contents/configuration difference(s)"
                      << (mem_content_diff > 40 ? " (the first 40 are listed)" : "") << "\n";
        // They are differences, and are counted as such.  They used to be printed and not counted, so a RAM or DSP configured
        // differently from its synthesis -- a width, a write mode, a cascade setting -- left the verdict at "0 differ".
        differ += mem_content_diff;
        if (mem_unpaired)
            std::cout << "  " << mem_unpaired
                      << " boundary group(s) named on one side only, so not checked\n";
    }

    // The hard blocks.  A block has no cones, so nothing above this looks at
    // one: the memories were cut at their boundary and everything else -- a
    // clock manager, a transceiver, its reference-clock buffer -- is simply
    // not part of a register-to-register comparison.  So say plainly which
    // ones the synthesis asked for and whether the extraction has them at all.
    //
    // This is the check that was missing when a design proved 36 obligations
    // with its transceiver reference clock switched off: the buffer was bound
    // to its site and then dropped before the bitstream was written, and
    // nothing in a cone comparison can notice an absent hard block.
    if (!hard_blocks.empty()) {
        std::map<std::string, int> by_type, missing_by_type;
        std::vector<std::string> unmodelled, absent, dropped;
        for (const auto &[cell, hb] : hard_blocks) {
            by_type[hb.type]++;
            if (hb.site.empty()) {
                dropped.push_back(cell + " (" + hb.type + ")");
                missing_by_type[hb.type]++;
                continue;
            }
            if (hb.gate_name.empty()) {
                unmodelled.push_back(cell + " (" + hb.type + " at " + hb.site + ")");
                missing_by_type[hb.type]++;
                continue;
            }
            bool found = false;
            for (const auto &inst : gate_m->instances) {
                const bool is_named = inst.name == hb.gate_name;
                const bool is_named_alt = !hb.gate_name_alt.empty() && inst.name == hb.gate_name_alt;
                if (is_named || is_named_alt) { found = true; break; }
            }
            if (!found) {
                absent.push_back(cell + " (" + hb.type + " at " + hb.site + ")");
                missing_by_type[hb.type]++;
            }
        }
        std::cout << "\nhard blocks: " << hard_blocks.size() << " placed by the synthesis";
        if (!by_type.empty()) {
            std::cout << " (";
            bool first = true;
            for (const auto &[t, n] : by_type) {
                std::cout << (first ? "" : ", ") << n << "x " << t;
                first = false;
            }
            std::cout << ")";
        }
        std::cout << "\n";
        auto name_them = [](const char *what, const std::vector<std::string> &v) {
            if (v.empty()) return;
            std::cout << "  " << v.size() << " " << what << ":\n";
            for (size_t i = 0; i < v.size() && i < 8; i++) std::cout << "    " << v[i] << "\n";
            if (v.size() > 8) std::cout << "    ... and " << (v.size() - 8) << " more\n";
        };
        name_them("DROPPED between synthesis and placement -- in the netlist, placed nowhere", dropped);
        name_them("the tile model does not model, so nothing here checks them", unmodelled);
        name_them("MISSING from the extraction -- placed by the synthesis, absent from the bitstream", absent);
        if (unmodelled.empty() && absent.empty() && dropped.empty())
            std::cout << "  all present in the extraction\n";
    }

    flush();
    auto secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::cout << "\n" << proved << " proved, " << differ << " differ, " << unknown << " unknown"
              << "   (" << secs << "s)\n";
    std::cout << "solver time " << solver_secs << "s over " << asked << " questions (" << trivial
              << " already constant after structural hashing), " << 1 + extra_sessions.size() << " session(s)\n";
    // A broken loop is not a detail of the run, it is a caveat on its verdict:
    // the constant it leaves behind deletes a dependency, so a cone can prove
    // -- or differ -- for want of an input rather than on the merits.  Say so
    // on every run that breaks one, next to the count that reads as a result.
    if (gold.loops_broken() || gate.loops_broken())
        std::cout << "combinational loops broken with a constant: "
                  << gold.loops_broken() << " gold, " << gate.loops_broken()
                  << " gate -- every cone downstream of one lost a dependency,\n"
                     "  so these results are conditional on those paths\n";
    if (!gold.free_nets().empty() || !gate.free_nets().empty())
        std::cout << "undriven nets treated as free: " << gold.free_nets().size() << " gold, "
                  << gate.free_nets().size() << " gate\n";
    return differ == 0 && unknown == 0 ? 0 : 1;
}

// A setup fault -- no solver on the machine, an unreadable database -- is not
// a verdict about the design, and must not be printed as one.
int main(int argc, char **argv)
{
    try {
        return run(argc, argv);
    } catch (const std::exception &e) {
        std::cerr << "lvs_equiv: " << e.what() << "\n";
        return 2;
    }
}
