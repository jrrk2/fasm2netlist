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

#include <algorithm>
#include <chrono>
#include <fstream>
#include <iostream>
#include <memory>
#include "json.hpp"

#include <regex>
#include <sstream>
#include <string>

using namespace lvs;

namespace {

void usage()
{
    std::cerr << "usage: lvs_equiv --gold <a.v> --gate <b.v> [--top NAME]\n"
                 "                 [--solver libz3|'cmd'] [--format dimacs|smt2]\n"
                 "                 [--dump-prefix PATH] [--quiet] [--explain] [--only TEXT]\n"
                 "\n"
                 "  --solver libz3  the linked library, one incremental session"
              << (have_linked_z3() ? " (default)\n" : " -- NOT IN THIS BUILD\n")
              << "  --solver <cmd>  any binary reading the chosen format, run per question\n";
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
    Solver solver{have_linked_z3() ? linked_z3_name() : "z3", Format::SmtLib2};
    bool quiet = false;
    // --explain: after a failure, say which named variables each side reads.
    bool explain = false;
    // --only TEXT: check just the registers whose name contains TEXT, for
    // going back to a failure without re-proving everything around it.
    std::string only;

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
        else if (a == "--compare") { std::string g = next(); compare.push_back({g, next()}); }
        else if (a == "--placement") placement_p = next();
        else if (a == "--gold-json") gold_json_p = next();
        else if (a == "--db") db = next();
        else if (a == "--device") device = next();
        else if (a == "--quiet") quiet = true;
        else if (a == "--only") only = next();
        else if (a == "--format") solver.format = (next() == "dimacs") ? Format::Dimacs : Format::SmtLib2;
        else { usage(); return 2; }
    }
    if (gold_path.empty() || gate_path.empty()) { usage(); return 2; }

    Netlist gold_nl, gate_nl;
    try {
        gold_nl = parse_verilog_file(gold_path);
        gate_nl = parse_verilog_file(gate_path);
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
    Cones gate(*gate_m, net, gate_to_gold);
    gate.set_mem_cuts(mem_cuts);

    // Match by any shared name, not just an identical one.  With --map the
    // gate's states already carry the gold's names, so this is an equality.
    std::vector<std::pair<std::string, std::string>> common;   // (gold, gate)
    {
        // Index the gate side by every name it could be matched on: the label
        // the placement gave it if it has one, else each of its own synonyms.
        // states() is a set, so "the first gate state that matches" is the
        // least one, and taking the minimum over the index says the same thing
        // as the scan it replaces -- without asking every state about every
        // other one, which on a SoC is half a million questions whose answers
        // are all the same handful of names.
        std::map<std::string, std::set<std::string>> gate_by_name;
        for (const auto &t : gate.states()) {
            auto mapped = gate_to_gold.find(t);
            if (mapped != gate_to_gold.end())
                gate_by_name[mapped->second].insert(t);
            else
                for (const auto &n : gate.synonyms(t)) gate_by_name[n].insert(t);
        }
        for (const auto &g : gold.states()) {
            const std::string *best = nullptr;
            for (const auto &n : gold.synonyms(g)) {
                auto it = gate_by_name.find(n);
                if (it == gate_by_name.end() || it->second.empty()) continue;
                const std::string &cand = *it->second.begin();
                if (!best || cand < *best) best = &cand;
            }
            if (best) common.emplace_back(g, *best);
        }
    }
    std::sort(common.begin(), common.end());

    std::cout << "registers: " << gold.states().size() << " gold, " << gate.states().size()
              << " gate, " << common.size() << " matched by name\n";
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

    auto check = [&](const std::string &label, Lit a, Lit b) {
        Lit miter = net.mk_xor(a, b);
        if (!dump_prefix.empty()) {
            // the same question in a form another solver can be handed
            std::string safe = label;
            for (char &c : safe) if (!isalnum((unsigned char)c)) c = '_';
            std::ofstream(dump_prefix + safe + (solver.format == Format::Dimacs ? ".cnf" : ".smt2"))
                << emit(net, miter, solver.format);
        }
        Result r = session->check(miter);
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

    for (const auto &[gn, tn] : compare)
        check(gn + " vs " + tn, gold.value_of(gn), gate.value_of(tn));
    if (!compare.empty() && common.empty()) {
        auto secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
        std::cout << "\n" << proved << " proved, " << differ << " differ, " << unknown
                  << " unknown   (" << secs << "s)\n";
        return differ == 0 && unknown == 0 ? 0 : 1;
    }

    for (const auto &[g, t] : common) {
        if (!only.empty() && g.find(only) == std::string::npos) continue;
        check(g == t ? g : (g + " = " + t), gold.next_state(g), gate.next_state(t));
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
    if (!mem_cuts.empty()) {
        const auto &gp = gold.mem_ports();
        const auto &tp = gate.mem_ports();
        // Pair by the symbol a memory's first read produces: the placement
        // already renamed the gate's to the gold's, so equal symbols are the
        // paired memories, whatever either side calls anything else.
        std::map<std::string, const Cones::MemPort *> by_sym;
        for (const auto &m : gp)
            if (!m.out_sym.empty()) by_sym[m.out_sym.front()] = &m;
        int mem_pairs = 0, mem_unpaired = 0, mem_rows = 0, mem_content_diff = 0;
        for (const auto &t : tp) {
            if (t.out_sym.empty()) continue;
            auto want = mem_cuts.find(t.out_sym.front());
            if (want == mem_cuts.end()) continue;
            auto g = by_sym.find(want->second);
            if (g == by_sym.end()) continue;
            mem_pairs++;
            const Cones::MemPort &G = *g->second;
            // The two sides list their boundary groups independently, so they
            // are paired by name.  A group only one side has is not silently
            // dropped: it is counted, because a boundary that is checked in
            // part is not a boundary that justifies a cut.
            std::map<std::string, const Cones::MemPort::Group *> gold_grp;
            for (const auto &g2 : G.boundary) gold_grp[g2.what] = &g2;
            for (const auto &tg : t.boundary) {
                auto gg = gold_grp.find(tg.what);
                if (gg == gold_grp.end()) { mem_unpaired++; continue; }
                const auto &gb = *gg->second;
                size_t n = std::max(tg.bits.size(), gb.bits.size());
                for (size_t i = 0; i < n; i++) {
                    // The synthesis's don't-cares win: the fabric always has
                    // something on a pin, and a pin the design never wired up
                    // is not a claim about the circuit.
                    if (i < gb.dontcare.size() && gb.dontcare[i]) continue;
                    if (i < tg.dontcare.size() && tg.dontcare[i]) continue;
                    check(t.where + " " + tg.what + "[" + std::to_string(i) + "]",
                          i < gb.bits.size() ? gb.bits[i] : LIT_FALSE,
                          i < tg.bits.size() ? tg.bits[i] : LIT_FALSE);
                }
                gold_grp.erase(gg);
            }
            mem_unpaired += int(gold_grp.size());

            // What the cut hides: the contents AND the configuration -- a
            // memory's widths and write modes, a DSP's inversion masks and
            // register enables.  Compared directly, because a boundary that
            // agrees says nothing about what the primitive does with it.
            std::set<std::string> rows;
            for (const auto &kv : G.contents) rows.insert(kv.first);
            for (const auto &kv : t.contents) rows.insert(kv.first);
            for (const auto &r : rows) {
                auto gi = G.contents.find(r), ti = t.contents.find(r);
                std::string gv = gi == G.contents.end() ? "0" : gi->second;
                std::string tv = ti == t.contents.end() ? "0" : ti->second;
                // A row the synthesis left undefined -- yosys writes the
                // unused parity rows as x -- says nothing about what the
                // memory should hold, exactly as a don't-care pin does at the
                // boundary.  The fabric always has some value there.
                if (gv.find('x') != std::string::npos) continue;
                mem_rows++;
                if (gv == tv) continue;
                mem_content_diff++;
                if (mem_content_diff <= 20)
                    std::cout << "  DIFFER  " << t.where << " " << r << ": gold " << gv
                              << ", gate " << tv << "\n";
            }
        }
        std::cout << "memories: " << gp.size() << " gold, " << tp.size() << " gate, "
                  << mem_pairs << " paired, " << mem_rows << " content rows compared\n";
        if (mem_content_diff)
            std::cout << "cut primitives: " << mem_content_diff
                      << " contents/configuration difference(s)\n";
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

    auto secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::cout << "\n" << proved << " proved, " << differ << " differ, " << unknown << " unknown"
              << "   (" << secs << "s)\n";
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
