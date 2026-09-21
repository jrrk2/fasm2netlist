// Prototype: FASM -> Verilog by INSTANTIATING a tile model, rather than by
// inferring what each slice "means".
//
// The whole point is that the only understanding of the FPGA lives in one
// place -- the model emitted at the top of the output -- so a fix there fixes
// every design.  This file just wires it up:
//
//   * nets come from the database: (tile, wire) pairs, joined across tile
//     boundaries by tileconn.json, so connectivity is a property of the
//     silicon rather than of this program;
//   * every routing feature in the FASM becomes one `assign`;
//   * every occupied slice becomes one `xclb` instance whose parameters are
//     the decoded configuration.
//
// BEST GUESSES, all of them in the model and none of them elsewhere:
//   - O6 = INIT[{A6..A1}], O5 = the low half read with A6 low.
//   - the main FF takes O6 / O5 / the X bypass / the slice's wide mux; XOR,
//     CY and MC31 are NOT modelled and select a tied 0 (the instance reports
//     it).
//   - the xMUX carries O6, O5, the 5FF's Q or the wide mux; XOR, CY and MC31
//     are not modelled.  F7/F8 has no site feature saying the mux EXISTS,
//     only features saying a column reads one, so the tree is built wherever
//     a column selects it, wired as nextpnr's own packer wires it.
//   - CE defaults to 1 and SR to 0 unless CEUSEDMUX / SRUSEDMUX say otherwise.
//   - carry and distributed RAM are modelled; SRL is not, and a slice using
//     one still gets an instance with its unmodelled features listed on
//     stderr.  Block RAM is not modelled either, but it is CUT: the block is
//     instantiated with its pins wired and nothing inside, so a comparison
//     can treat its reads as free variables and its inputs as obligations.
//     lvs_equiv keeps its OWN column model in cone.cpp and must agree with
//     this one; the two are kept honest by the examples, not by sharing code.
#include "json.hpp"
#include "lvs/regmap.hpp"
#include "lvs/tileconfig.hpp"

#include "bram_ports.hpp"
#include "dsp_ports.hpp"

#include <algorithm>
#include <fstream>
#include <iostream>
#include <array>
#include <map>
#include <set>
#include <regex>
#include <cstring>
#include <sstream>

using namespace lvs;

namespace {

std::string readFile(const std::string &p)
{
    std::ifstream f(p);
    if (!f) throw std::runtime_error("cannot open " + p);
    std::ostringstream ss; ss << f.rdbuf(); return ss.str();
}

std::string sanitise(const std::string &s)
{
    std::string r;
    for (char c : s) r.push_back(isalnum((unsigned char)c) ? c : '_');
    return r;
}

bool ends_with(const std::string &s, const char *suf)
{
    size_t n = strlen(suf);
    return s.size() >= n && s.compare(s.size() - n, n, suf) == 0;
}

// Direction of one IOB site feature (the part after `IOB_Yn.`).  A DRIVE or
// trailing .OUT configures an OBUF; .IN / .IN_ONLY / .IN_DIFF and the HP-bank
// glue configure an IBUF.  IN_TERM is termination, not an input buffer.  The
// two sets do not overlap on a unidirectional pad -- the same observation
// classifyIob in main.cpp makes on the Johnson example.
bool iob_feat_is_out(const std::string &rest)
{
    const bool has_drive = rest.find(".DRIVE.") != std::string::npos
                           || rest.rfind("DRIVE.", 0) == 0;
    const bool has_out = ends_with(rest, ".OUT") || rest == "OUT";
    return has_drive || has_out;
}
bool iob_feat_is_in(const std::string &rest)
{
    const bool hp_glue = rest == "IBUF_HP_BANK_GLUE" || rest == "IBUFDS_BANK_GLUE";
    const bool in_tag = ends_with(rest, ".IN") || ends_with(rest, ".IN_ONLY")
                        || ends_with(rest, ".IN_DIFF") || rest == "IN"
                        || rest == "IN_ONLY" || rest == "IN_DIFF";
    return hp_glue || in_tag;
}

struct Dsu
{
    std::map<std::string, std::string> parent;
    const std::string &find(const std::string &x)
    {
        auto it = parent.find(x);
        if (it == parent.end()) return parent[x] = x;
        if (it->second == x) return it->second;
        return parent[x] = find(it->second);
    }
    void unite(const std::string &a, const std::string &b)
    {
        std::string ra = find(a), rb = find(b);
        if (ra != rb) parent[ra] = rb;
    }
};

struct TileInfo
{
    std::string type;
    int x = 0, y = 0;
    std::vector<std::pair<std::string, std::string>> sites; // (site name, site type) in x order
};

} // namespace

int main(int argc, char **argv)
{
    std::string fasm, db, device = "xc7vx485t", out_path, model_path, xdc_path, part;
    std::string placement_path, gold_json_path;
    std::vector<std::string> input_pats;   // substrings naming genuinely external nets
    int hops = 0;                          // rounds of reachability growth
    bool simple_clock = true;              // see the note on the clock tree below
    bool use_default_ppips = false;        // `default` ppips: off until justified
    int pullup = 1;                        // value an undriven routing net reads
    // --timing: every routing assign carries the database's transport delay
    // (#(fast_min:slow_max:slow_max), ns) and the slice model a specify
    // block, so the netlist can be timed -- simulated with iverilog -Tmin /
    // -Tmax, or walked by an STA -- without an SDF.
    bool timing = false;
    std::string net_delays_path;           // --net-delays: driver site pin -> load site pin, min/max ns
    for (int i = 1; i < argc; i++) {
        std::string a = argv[i];
        auto next = [&] { return (i + 1 < argc) ? std::string(argv[++i]) : std::string(); };
        if (a == "--fasm") fasm = next();
        else if (a == "--db") db = next();
        else if (a == "--device") device = next();
        else if (a == "--out") out_path = next();
        else if (a == "--model-out") model_path = next();
        else if (a == "--xdc") xdc_path = next();
        else if (a == "--part") part = next();
        else if (a == "--input") input_pats.push_back(next());
        else if (a == "--hops") hops = atoi(next().c_str());
        else if (a == "--routed-clock") simple_clock = false;
        else if (a == "--pullup") pullup = atoi(next().c_str());
        else if (a == "--default-ppips") use_default_ppips = true;
        else if (a == "--placement") placement_path = next();
        else if (a == "--gold-json") gold_json_path = next();
        else if (a == "--timing") timing = true;
        else if (a == "--net-delays") { net_delays_path = next(); timing = true; }
        else { std::cerr << "usage: tileverilog --fasm f.fasm --db <prjxray-db>/<family> "
                            "[--device xc7vx485t] [--out out.v]\n"
                            "                   [--input <substring>]...  nets driven from outside\n"; return 2; }
    }
    if (fasm.empty() || db.empty()) { std::cerr << "need --fasm and --db\n"; return 2; }

    DesignConfig dc = read_fasm(fasm);

    // Tiles the placement puts a RAMB36E1 in; see the block RAM section.
    std::set<std::string> ramb36_tiles;
    if (!placement_path.empty()) {
        try {
            json::Value place = json::parse(readFile(placement_path));
            for (const auto &pv : place.members())
                if (pv.second.get("bel").asString() == "RAMB36E1")
                    ramb36_tiles.insert(pv.second.get("tile").asString());
        } catch (const std::exception &e) {
            std::cerr << "  placement: not read for RAMB36 sites (" << e.what() << ")\n";
        }
    }

    // ---- database -------------------------------------------------------
    json::Value grid = json::parse(readFile(db + "/" + device + "/tilegrid.json"));
    std::map<std::string, TileInfo> tiles;
    std::map<std::pair<int, int>, std::string> by_xy;
    for (const auto &kv : grid.members()) {
        TileInfo ti;
        ti.type = kv.second.get("type").asString();
        ti.x = int(kv.second.get("grid_x").asInt());
        ti.y = int(kv.second.get("grid_y").asInt());
        std::vector<std::pair<int, std::pair<std::string, std::string>>> ss;
        for (const auto &sv : kv.second.get("sites").members()) {
            int sx = 0;
            auto p = sv.first.find('X');
            if (p != std::string::npos) sx = atoi(sv.first.c_str() + p + 1);
            ss.push_back({sx, {sv.first, sv.second.asString()}});
        }
        std::sort(ss.begin(), ss.end());
        for (auto &s : ss) ti.sites.push_back(s.second);
        tiles[kv.first] = ti;
        by_xy[{ti.x, ti.y}] = kv.first;
    }

    // which tiles matter: those the FASM mentions
    std::set<std::string> used;
    for (const auto &kv : dc.slices) used.insert(kv.second.tile);
    for (const auto &kv : dc.other_tiles) used.insert(kv.first);

    // tileconn lives per-device in some families and per-family in others
    auto tileconn_path = [&] {
        std::string per_device = db + "/" + device + "/tileconn.json";
        std::ifstream probe(per_device);
        return probe ? per_device : db + "/tileconn.json";
    }();
    json::Value tc = json::parse(readFile(tileconn_path));

    // The XDC names the design's pads; pull their tiles in before the net
    // closure, or the pad wires never enter the graph and cannot be labelled.
    std::vector<std::pair<std::string, std::string>> xdc_ports;   // (port, pin)
    std::map<std::string, std::pair<std::string, std::string>> pin_site;  // pin -> (site, tile)
    if (!xdc_path.empty() && !part.empty()) {
        std::ifstream pf(db + "/" + part + "/package_pins.csv");
        std::string line;
        std::getline(pf, line);
        while (std::getline(pf, line)) {
            std::vector<std::string> f;
            std::string cur;
            for (char c : line) { if (c == ',') { f.push_back(cur); cur.clear(); } else cur.push_back(c); }
            f.push_back(cur);
            if (f.size() >= 4) pin_site[f[0]] = {f[2], f[3]};
        }
        std::ifstream xf(xdc_path);
        // `set_property PACKAGE_PIN <pin> [get_ports <name>]`, plain or -dict,
        // with the port optionally braced: {led[0]} keeps its subscript.
        // The port name may be braced ({led[0]}) or bare (led[0]).  Bare, it
        // can still carry a bus index, so a complete [digits] group is part of
        // the name while a lone ] closes the [get_ports ...] around it.
        static const std::regex re(R"((?:PACKAGE_PIN|LOC)\s+(\S+).*?get_ports\s*(?:\{\s*([^\}]+?)\s*\}|((?:[^\[\]\s]|\[\d+\])+)))");
        while (std::getline(xf, line)) {
            std::smatch m;
            if (!std::regex_search(line, m, re)) continue;
            std::string port = m[2].matched ? m[2].str() : m[3].str();
            xdc_ports.push_back({port, m[1].str()});
            auto ps = pin_site.find(m[1].str());
            if (ps != pin_site.end()) used.insert(ps->second.second);
        }
        std::cerr << "  XDC: " << xdc_ports.size() << " pin constraint(s)\n";
    }

    // site pins per tile type, from tile_type_*.json
    std::map<std::string, std::vector<std::map<std::string, std::string>>> site_pins; // type -> per-site pin->wire
    // ...and what FASM calls each of those sites, in the same order.  A tile
    // type describes its sites positionally and by coordinate ("prefix"
    // RAMB18, "y_coord" 0); FASM names them "RAMB18_Y0".  Knowing the FASM
    // spelling is what lets a site's configuration be told apart from a PIP,
    // since the two are written identically -- "<tile>.<a>.<b>" either way.
    std::map<std::string, std::vector<std::string>> site_names;   // type -> per-site FASM name
    // The database's timing for a PIP: delay at the four corners (ns), the
    // capacitance it loads its source with (pF) and its output resistance
    // (mOhm) -- Project X-Ray's RC model, the one nextpnr's chipdb is built
    // from.  Keyed by "src\ndst" within the type.  A wire's own cap/res too.
    struct PipT { double fmin = 0, fmax = 0, smin = 0, smax = 0, in_cap = 0, res = 0; };
    std::map<std::string, std::map<std::string, PipT>> pip_timing;              // type -> "src\ndst"
    std::map<std::string, std::map<std::string, std::pair<double, double>>> wire_rc; // type -> wire -> (cap, res)
    auto num = [](const json::Value &v) { return v.isNull() || v.isString() ? (v.isString() ? atof(v.asString().c_str()) : 0.0) : v.asDouble(); };
    auto load_type = [&](const std::string &type) {
        if (site_pins.count(type)) return;
        std::string path = db + "/tile_type_" + type + ".json";
        std::ifstream probe(path);
        if (!probe) { site_pins[type] = {}; return; }
        json::Value tt = json::parse(readFile(path));
        if (timing) {
            auto &pt = pip_timing[type];
            for (const auto &pk : tt.get("pips").members()) {
                const json::Value &p = pk.second;
                std::string sw = p.get("src_wire").asString(), dw = p.get("dst_wire").asString();
                auto take = [&](const json::Value &d, const std::string &key) {
                    if (d.isNull()) return;
                    PipT t;
                    const json::Value &dl = d.get("delay");
                    if (!dl.isNull()) {
                        const auto &a = dl.items();
                        if (a.size() >= 4) { t.fmin = num(a[0]); t.fmax = num(a[1]); t.smin = num(a[2]); t.smax = num(a[3]); }
                    }
                    t.in_cap = num(d.get("in_cap")); t.res = num(d.get("res"));
                    pt[key] = t;
                };
                take(p.get("src_to_dst"), sw + "\n" + dw);
                if (p.get("is_directional").asString() == "0") take(p.get("dst_to_src"), dw + "\n" + sw);
            }
            auto &wr = wire_rc[type];
            for (const auto &wk : tt.get("wires").members())
                if (!wk.second.isNull()) wr[wk.first] = {num(wk.second.get("cap")), num(wk.second.get("res"))};
        }
        std::vector<std::map<std::string, std::string>> per;
        std::vector<std::string> names;
        for (const auto &s : tt.get("sites").items()) {
            std::map<std::string, std::string> m;
            for (const auto &pk : s.get("site_pins").members())
                m[pk.first] = pk.second.get("wire").asString();
            per.push_back(m);
            const json::Value &pre = s.get("prefix"), &yc = s.get("y_coord");
            names.push_back(pre.isNull() || yc.isNull()
                                ? std::string()
                                : pre.asString() + "_Y" + std::to_string(yc.asInt()));
        }
        site_pins[type] = per;
        site_names[type] = names;
    };
    for (const auto &t : used) if (tiles.count(t)) load_type(tiles[t].type);

    // ---- pseudo-PIPs: the connections that carry no bits ------------------
    // ppips_<type>.db lists hardwired paths.  `always` is permanently on and
    // appears in no bitstream, so a net graph built only from FASM features is
    // missing them -- which leaves, among others, every slice's X bypass
    // undriven and sitting at the pull-up.  `default` is on unless the
    // destination is driven by a real PIP, so it is applied only where nothing
    // else drives it.  `hint` is documentation and is ignored.
    std::map<std::string, std::vector<std::array<std::string, 3>>> ppips; // type -> (dst,src,kind)
    auto load_ppips = [&](const std::string &type) {
        if (ppips.count(type)) return;
        std::string lower;
        for (char c : type) lower.push_back(char(tolower(c)));
        std::ifstream in(db + "/ppips_" + lower + ".db");
        std::vector<std::array<std::string, 3>> v;
        std::string line;
        while (std::getline(in, line)) {
            std::istringstream ls(line);
            std::string feat, kind;
            if (!(ls >> feat >> kind)) continue;
            auto d1 = feat.find('.');
            if (d1 == std::string::npos) continue;
            auto d2 = feat.find('.', d1 + 1);
            if (d2 == std::string::npos) continue;
            v.push_back({feat.substr(d1 + 1, d2 - d1 - 1), feat.substr(d2 + 1), kind});
        }
        ppips[type] = v;
    };
    for (const auto &t : used) if (tiles.count(t)) load_ppips(tiles[t].type);

    // ---- nets: (tile,wire), joined across tile boundaries ---------------
    Dsu dsu;
    auto tw = [](const std::string &t, const std::string &w) { return t + "/" + w; };

    // Which (tile,wire) endpoints the design actually touches.  A route runs
    // through tiles that set no bit and so appear nowhere in the FASM, which
    // is why joining only the named tiles leaves the clock spine in pieces.
    // Grow from the known endpoints instead: join a wire pair when either end
    // is already reachable, and repeat.  That follows the design's own
    // connectivity rather than a radius, so it closes the chain without
    // dragging in the rest of the die.
    std::set<std::string> known;
    // ...and which wires a real PIP drives, which is what a "default"
    // pseudo-PIP has to defer to.  Collected here because this is already the
    // pass that reads the features, and the pseudo-PIPs are now applied during
    // growth rather than after it.
    std::set<std::string> pip_driven;
    for (const auto &kv : dc.other_tiles) {
        auto ti = tiles.find(kv.first);
        const std::vector<std::string> *sn =
            ti == tiles.end() ? nullptr : &site_names[ti->second.type];
        for (const auto &feat : kv.second) {
            auto dot = feat.find('.');
            if (dot == std::string::npos) continue;
            // A site's configuration has the same shape as a PIP; taking it
            // for one puts wires in the net graph that the tile does not have.
            if (sn && std::find(sn->begin(), sn->end(), feat.substr(0, dot)) != sn->end()) continue;
            if (feat.find('.', dot + 1) != std::string::npos) continue;
            known.insert(tw(kv.first, feat.substr(0, dot)));
            known.insert(tw(kv.first, feat.substr(dot + 1)));
            pip_driven.insert(tw(kv.first, feat.substr(0, dot)));
        }
    }
    // The same set before the pseudo-PIPs are added to it: what the design
    // ROUTED, as opposed to what is hardwired.  See the latch note below.
    const std::set<std::string> real_pip_driven = pip_driven;
    // ...and the wires those PIPs read FROM: what the routing consumes.  A
    // column whose output feeds a PIP is in use whatever its features say.
    std::set<std::string> real_pip_sources;
    for (const auto &kv : dc.other_tiles) {
        auto ti = tiles.find(kv.first);
        const std::vector<std::string> *sn =
            ti == tiles.end() ? nullptr : &site_names[ti->second.type];
        for (const auto &feat : kv.second) {
            auto dot = feat.find('.');
            if (dot == std::string::npos) continue;
            if (sn && std::find(sn->begin(), sn->end(), feat.substr(0, dot)) != sn->end()) continue;
            if (feat.find('.', dot + 1) != std::string::npos) continue;
            real_pip_sources.insert(tw(kv.first, feat.substr(dot + 1)));
        }
    }
    for (const auto &kv : dc.slices) {
        auto ti = tiles.find(kv.second.tile);
        if (ti == tiles.end()) continue;
        int ordinal = kv.second.site.back() - '0';
        const auto &per = site_pins[ti->second.type];
        if (ordinal < int(per.size()))
            for (const auto &pw : per[ordinal]) known.insert(tw(kv.second.tile, pw.second));
    }
    // The pads, likewise.  A pad reaches the fabric over hops that set no
    // bit -- IOB to IBUF, IBUF to the ILOGIC's D, its O to LOGIC_OUTS -- and
    // the growth below applies a hardwired hop only from an endpoint it
    // already knows.  nextpnr's FASM writes those hops and so names the
    // wires; a bitstream shows an input pad only as its IOB's site features,
    // and the XDC only names its tile.  Seeding the IOB's own pins is what
    // lets a Vivado bitstream's reset reach the reset synchroniser.
    //
    // Seeding also puts the receive side of an output-only pad in the graph.
    // That is intentional -- the hops are real -- but the XDC must not name
    // that wire; see the labelling loop, which takes direction from the FASM.
    for (const auto &t : used) {
        auto it = tiles.find(t);
        if (it == tiles.end()) continue;
        if (it->second.type.find("IOB") == std::string::npos) continue;
        load_type(it->second.type);
        for (const auto &per : site_pins[it->second.type])
            for (const auto &pw : per) known.insert(tw(t, pw.second));
    }

    std::map<std::string, std::vector<std::string>> tiles_by_type;
    for (const auto &kv : tiles) tiles_by_type[kv.second.type].push_back(kv.first);

    // Run to a fixpoint rather than a fixed number of rounds.  Growth walks
    // the segments of a physical wire, so a round is one tile of travel and
    // the number needed is the length of the longest wire the design uses: a
    // fixed four reaches an EE4 and stops one short of nothing in particular,
    // which silently cut every SE6 in nextpnr's arty example and left three
    // of its four switch inputs unconnected to the logic that reads them.
    // The loop already stops when a round adds nothing, so the fixpoint is
    // what the cap was truncating; the cap remains only as a guard against a
    // database that cycles, and says so if it is ever hit.
    // Growth is a fixpoint over a finite set -- every round adds at least one
    // (tile,wire) endpoint or stops -- so it terminates on its own, and the
    // cap is insurance against a cyclic database rather than a schedule.  It
    // was 64, and 64 was not enough: this SoC needs more, and the rounds it
    // was not given were the ones that carry a signal out of a hard block and
    // across the tiles that hold nothing but hardwiring.  Truncating growth
    // does not fail, it silently returns a net with one end missing.
    const int kMaxRounds = 1024;

    // The scan follows the frontier, not the die.  A round can only add an
    // endpoint next to one already known, so there is no reason to visit a
    // tile that has no known endpoint in it -- and visiting all of them is
    // what made the fixpoint expensive, since the whole grid was re-examined
    // once per round.  Indexing the tile-connection entries by tile type, on
    // both sides, lets a round cost the design's own footprint instead.
    std::map<std::string, std::vector<const json::Value *>> conn_by_type;
    for (const auto &e : tc.items()) {
        const auto &types = e.get("tile_types").items();
        const auto &deltas = e.get("grid_deltas").items();
        if (types.size() != 2 || deltas.size() != 2) continue;
        conn_by_type[types[0].asString()].push_back(&e);
        conn_by_type[types[1].asString()].push_back(&e);
    }

    auto tile_of = [](const std::string &endpoint) {
        auto slash = endpoint.find('/');
        return slash == std::string::npos ? endpoint : endpoint.substr(0, slash);
    };
    std::set<std::string> frontier_tiles;
    for (const auto &k : known) frontier_tiles.insert(tile_of(k));

    int joins = 0, rounds = 0, n_always = 0, n_default = 0;
    bool settled = false;
    std::vector<std::pair<std::string, std::string>> ppip_assigns;   // dst, src
    // Which `always` source already drives a destination.  A wire cannot have
    // two hardwired drivers, so a second `always` into the same destination is
    // the same site output under another name -- BRAM_RAMB18_DOADO0 and
    // BRAM_FIFO36_DOADOU0 are one pin, seen as the 18Kb half and as the 36Kb
    // block.  Skipping the second left whichever alias sorted later
    // unconnected: the upper RAMB18's data outputs went nowhere in a Vivado
    // bitstream, whose FASM names neither (both are bit-less) while nextpnr
    // writes the one it used.  Joining the aliases into one node is what the
    // silicon does.
    std::map<std::string, std::string> always_src_of;
    for (int round = 0; round < (hops > 0 ? hops : kMaxRounds); round++) {
        rounds = round + 1;
        size_t before = known.size();
        std::set<std::string> next_tiles;
        for (const auto &t : frontier_tiles) {
            auto self = tiles.find(t);
            if (self == tiles.end()) continue;
            auto entries = conn_by_type.find(self->second.type);
            if (entries == conn_by_type.end()) continue;
            for (const json::Value *e : entries->second) {
                const auto &types = e->get("tile_types").items();
                const auto &deltas = e->get("grid_deltas").items();
                int dx = int(deltas[0].asInt()), dy = int(deltas[1].asInt());
                // This tile may be either end of the entry; as the second, the
                // neighbour lies in the opposite direction and the wire pair
                // reads the other way round.
                for (int side = 0; side < 2; side++) {
                    if (types[side].asString() != self->second.type) continue;
                    int sx = side ? -dx : dx, sy = side ? -dy : dy;
                    auto nb = by_xy.find({self->second.x + sx, self->second.y + sy});
                    if (nb == by_xy.end() || tiles[nb->second].type != types[1 - side].asString())
                        continue;
                    for (const auto &wp : e->get("wire_pairs").items()) {
                        if (wp.items().size() != 2) continue;
                        std::string a = tw(t, wp.items()[side].asString());
                        std::string b = tw(nb->second, wp.items()[1 - side].asString());
                        bool ka = known.count(a), kb = known.count(b);
                        if (!ka && !kb) continue;
                        dsu.unite(a, b);
                        if (!ka) { known.insert(a); next_tiles.insert(t); }
                        if (!kb) { known.insert(b); next_tiles.insert(nb->second); }
                        joins++;
                    }
                }
            }
        }
        // The hardwired hops, in the same fixpoint.  A pseudo-PIP carries no
        // configuration bit, so the tile it lives in can appear nowhere in the
        // FASM -- and the tiles that hold nothing BUT hardwiring are exactly
        // the ones a signal leaving a hard block passes through.  Applying
        // these only to tiles the FASM names left an MMCM's LOCKED sitting on
        // INT_INTERFACE_LOGIC_OUTS_L_B18 with nothing to carry it the one hop
        // to LOGIC_OUTS_L18, where the interconnect could pick it up.
        //
        // And they belong INSIDE the loop, not after it: a hop makes a new
        // endpoint reachable, and what that endpoint reaches is more tile
        // connections, which is another round's work.  Run afterwards, the
        // graph stops one hop short of wherever the last hardwired link was.
        {
            std::vector<std::string> visit(frontier_tiles.begin(), frontier_tiles.end());
            visit.insert(visit.end(), next_tiles.begin(), next_tiles.end());
            for (const auto &t : visit) {
                auto it = tiles.find(t);
                if (it == tiles.end()) continue;
                load_ppips(it->second.type);
                for (const auto &pp : ppips[it->second.type]) {
                    if (pp[2] == "hint") continue;
                    if (pp[2] == "default" && !use_default_ppips) continue;
                    std::string dst = tw(t, pp[0]), src = tw(t, pp[1]);
                    bool kd = known.count(dst), ks = known.count(src);
                    if (!kd && !ks) continue;
                    if (pip_driven.count(dst)) {
                        auto prev = always_src_of.find(dst);
                        if (pp[2] == "always" && prev != always_src_of.end() && prev->second != src) {
                            dsu.unite(src, prev->second);
                            if (!ks) { known.insert(src); next_tiles.insert(t); }
                        }
                        continue;
                    }
                    ppip_assigns.push_back({dst, src});
                    pip_driven.insert(dst);
                    if (pp[2] == "always") always_src_of[dst] = src;
                    dsu.find(dst); dsu.find(src);
                    if (!kd) { known.insert(dst); next_tiles.insert(t); }
                    if (!ks) { known.insert(src); next_tiles.insert(t); }
                    (pp[2] == "always" ? n_always : n_default)++;
                }
            }
        }
        if (known.size() == before) { settled = true; break; }
        frontier_tiles.swap(next_tiles);
    }
    // Said after the loop, and only when the loop is what stopped: the test
    // used to be "we reached round 64", which is not the same thing -- it
    // fired on the round the cap happens to name even when the cap had been
    // raised and the growth went on to finish, so a real truncation and a
    // healthy long run were reported identically.
    if (!settled)
        std::cerr << "  warning: net growth did not settle in " << rounds
                  << " rounds; some nets may be incomplete\n";
    std::cerr << "  pseudo-PIPs applied: " << n_always << " always, " << n_default
              << " default\n";


    // ---- I/O: the fabric's edge ------------------------------------------
    // An IOB or IOI site is a buffer this prototype does not model, so the nets
    // on its pins have no driver inside the fabric and would otherwise sit at
    // the pull-up.  They are the design's actual boundary: expose them as
    // ports, taking the direction from whether the fabric drives the net or
    // reads it.  This is what turns "everything reads 1" into a testbench that
    // can drive a reset and observe an LED.
    std::set<std::string> io_endpoints;
    for (const auto &t : used) {
        auto it = tiles.find(t);
        if (it == tiles.end()) continue;
        const std::string &ty = it->second.type;
        bool is_io = ty.find("IOB") != std::string::npos || ty.find("IOI") != std::string::npos;
        if (!is_io) continue;
        load_type(ty);
        for (const auto &per : site_pins[ty])
            for (const auto &pw : per)
                io_endpoints.insert(tw(t, pw.second));
    }

    // ---- the clock tree, simplified --------------------------------------
    // Not reconstructed: every slice clock is joined straight to the BUFG
    // output that drives it.  The real path (BUFGCTRL -> CLK_HROW -> HCLK ->
    // INT -> CLB) crosses tiles that set no bits and so appear nowhere in the
    // FASM, which leaves the chain in pieces however the net graph is grown.
    // Treating the buffer output as the clock source is what the rest of the
    // toolchain does too, and it is honest about being a simplification --
    // --routed-clock turns it off and leaves the pieces visible.
    std::vector<std::string> bufg_outs;
    for (const auto &kv : dc.other_tiles) {
        if (kv.first.rfind("CLK_BUFG", 0) != 0) continue;
        for (const auto &feat : kv.second) {
            auto dot = feat.find('.');
            if (dot == std::string::npos) continue;
            for (const std::string &w : {feat.substr(0, dot), feat.substr(dot + 1)}) {
                if (w.rfind("CLK_BUFG_BUFGCTRL", 0) == 0 && w.size() > 2 &&
                    w.compare(w.size() - 2, 2, "_O") == 0)
                    bufg_outs.push_back(tw(kv.first, w));
            }
        }
    }
    std::sort(bufg_outs.begin(), bufg_outs.end());
    bufg_outs.erase(std::unique(bufg_outs.begin(), bufg_outs.end()), bufg_outs.end());

    int clocked = 0;
    if (simple_clock && bufg_outs.empty()) {
        // No BUFG output is named in the FASM.  The simplification still
        // holds -- every slice clock is the same net, arriving from outside --
        // so unify them on the first one and let it become a port.
        for (const auto &kv : dc.slices) {
            auto ti = tiles.find(kv.second.tile);
            if (ti == tiles.end()) continue;
            int ordinal = kv.second.site.back() - '0';
            const auto &per = site_pins[ti->second.type];
            if (ordinal >= int(per.size())) continue;
            auto pin = per[ordinal].find("CLK");
            if (pin == per[ordinal].end()) continue;
            bufg_outs.push_back(tw(kv.second.tile, pin->second));
        }
        if (!bufg_outs.empty()) bufg_outs.resize(1);
    }
    // Joining every slice clock to one BUFG is only sound when there is one
    // BUFG.  A design with several has several clock domains, and merging
    // them would say two registers share a clock when the bitstream says they
    // do not -- a claim the checker would then happily prove.  With more than
    // one, the routing has to answer the question instead.
    bool one_clock = bufg_outs.size() == 1;
    if (simple_clock && one_clock) {
        for (const auto &kv : dc.slices) {
            auto ti = tiles.find(kv.second.tile);
            if (ti == tiles.end()) continue;
            int ordinal = kv.second.site.back() - '0';
            const auto &per = site_pins[ti->second.type];
            if (ordinal >= int(per.size())) continue;
            auto pin = per[ordinal].find("CLK");
            if (pin == per[ordinal].end()) continue;
            dsu.unite(tw(kv.second.tile, pin->second), bufg_outs.front());
            clocked++;
        }
    }

    // ---- routing features: one assign each -------------------------------
    std::vector<std::pair<std::string, std::string>> assigns; // dst, src

    // I/O sites holding a DDR register rather than a wire.  Recorded here and
    // emitted further down, where net() exists: an instance pin written with a
    // different spelling from the rest of the netlist splits the net in two.
    struct DdrSite {
        std::string tile, site, prim, iname;             // IDDR or ODDR
        std::vector<std::pair<std::string, std::string>> ports; // port, tile wire
    };
    std::vector<DdrSite> ddr_sites;
    // A non-slice site's configuration, kept against the site that set it.
    // These are the features the model reads to know what a hard block is
    // configured as; the ones it has no use for are still counted, so the
    // report says how much of the bitstream went unread.
    std::map<std::string, std::map<std::string, std::vector<std::string>>> site_feats; // tile -> site -> features
    int skipped_site_cfg = 0;
    for (const auto &kv : dc.other_tiles) {
        const std::string &tile = kv.first;
        auto ti = tiles.find(tile);
        const std::vector<std::string> *sn =
            ti == tiles.end() ? nullptr : &site_names[ti->second.type];
        for (const auto &feat : kv.second) {
            auto dot = feat.find('.');
            // "<site>.<feature>" and "<dstwire>.<srcwire>" are the same shape,
            // so the only thing that tells them apart is whether the first
            // component names a site of this tile.  Reading a site's
            // configuration as a PIP is not harmless: it invents a net called
            // RAMB18_Y0 driven by one called IN_USE, and every such pair is a
            // wire the design does not have.
            if (dot != std::string::npos && sn) {
                std::string head = feat.substr(0, dot);
                if (std::find(sn->begin(), sn->end(), head) != sn->end()) {
                    site_feats[tile][head].push_back(feat.substr(dot + 1));
                    continue;
                }
            }
            if (dot == std::string::npos || feat.find('.', dot + 1) != std::string::npos) {
                skipped_site_cfg++;   // site config for a non-slice site, not a PIP
                continue;
            }
            std::string dstw = feat.substr(0, dot), srcw = feat.substr(dot + 1);
            assigns.push_back({tw(tile, dstw), tw(tile, srcw)});
            dsu.find(tw(tile, dstw));
            dsu.find(tw(tile, srcw));
        }
    }


    // The pseudo-PIPs were applied during growth, above; fold them in now that
    // the FASM's own routing features have been read.
    assigns.insert(assigns.end(), ppip_assigns.begin(), ppip_assigns.end());

    // ---- where the block RAMs are ----------------------------------------
    // Worked out once: the clock tree needs it below, and the instances that
    // get emitted further down need it again.
    struct BramSite
    {
        std::string tile, site, cfg_site;
        const char *prefix;
        bool is36;
        std::map<std::string, std::string> canon;   // canonical port -> tile wire
    };
    std::vector<BramSite> bram_sites;
    for (const auto &tf : site_feats) {
        const std::string &tile = tf.first;
        auto ti = tiles.find(tile);
        if (ti == tiles.end() || ti->second.type.rfind("BRAM_", 0) != 0) continue;
        const auto &per = site_pins[ti->second.type];
        // The three sites in a BRAM tile spell their PINS differently (prjxray
        // types the lower 18Kb one FIFO18E1, so its pins carry FIFO names) but
        // every site's WIRES are named after the primitive's own ports, so the
        // port name reads off the wire and needs no translation table.
        auto canon_of = [&](const char *prefix) {
            std::map<std::string, std::string> c;
            for (const auto &m : per) {
                if (m.empty()) continue;
                bool all = true;
                for (const auto &pw : m)
                    if (pw.second.rfind(prefix, 0) != 0) { all = false; break; }
                if (!all) continue;
                for (const auto &pw : m) c[pw.second.substr(strlen(prefix))] = pw.second;
                break;
            }
            return c;
        };
        // 36Kb mode has no configuration bit of its own: prjxray's RAMB36 tags
        // are all "this bit is clear", so a plain RAMB36 emits none of them.
        // What does say so is which site's pins the tile's routing touches --
        // the same test src/cells_bram.cpp makes, off the same features.  A
        // 36Kb memory's control pins are still configured on its lower half.
        bool is36 = false;
        auto ot = dc.other_tiles.find(tile);
        if (ot != dc.other_tiles.end())
            for (const auto &f : ot->second)
                if (f.find("BRAM_FIFO36_") != std::string::npos) { is36 = true; break; }
        // ...which only nextpnr's FASM can say: those FIFO36 hops are
        // bit-less pseudo-PIPs, so bit2fasm never writes them, and a 36Kb
        // block at width 18 or 36 IS two 18Kb halves at half the width with
        // the address shared and the data split -- the same bits and the
        // same routing as two independent RAMB18s that happen to share an
        // address bus, which a memory split into width-grains does all the
        // time.  No configuration bit distinguishes them because no hardware
        // does.  The one witness is which site the design asked for, and the
        // placement says so -- the same external fact the XDC supplies for a
        // pad's name.
        if (ramb36_tiles.count(tile)) is36 = true;
        if (is36) {
            bram_sites.push_back({tile, "RAMB36_Y0", "RAMB18_Y0", "BRAM_FIFO36_", true,
                                  canon_of("BRAM_FIFO36_")});
        } else {
            for (const auto &sf : tf.second) {
                const char *prefix = sf.first == "RAMB18_Y0"   ? "BRAM_FIFO18_"
                                     : sf.first == "RAMB18_Y1" ? "BRAM_RAMB18_"
                                                               : nullptr;
                if (!prefix) continue;
                bram_sites.push_back({tile, sf.first, sf.first, prefix, false, canon_of(prefix)});
            }
        }
    }

    // A block RAM is clocked by the same one BUFG as everything else, on the
    // same argument the slices are joined on above: with a single clock in the
    // design there is only one thing its clock pins can be.  Without this the
    // memory's clock pin sits on the interconnect pull-up, and a boundary that
    // compares a clock against a constant fails for a reason that has nothing
    // to do with the design.
    if (simple_clock && one_clock)
        for (const auto &b : bram_sites)
            for (const char *pin : {"CLKARDCLK", "CLKBWRCLK", "REGCLKARDRCLK", "REGCLKB",
                                    "CLKARDCLKL", "CLKARDCLKU", "CLKBWRCLKL", "CLKBWRCLKU",
                                    "REGCLKARDRCLKL", "REGCLKARDRCLKU", "REGCLKBL",
                                    "REGCLKBU"}) {
                auto it = b.canon.find(pin);
                if (it != b.canon.end()) dsu.unite(tw(b.tile, it->second), bufg_outs.front());
            }

    // With the tree simplified, the clock net's own routing features -- real
    // and pseudo alike -- drive it from pieces of a path we have replaced.
    std::string clock_root;
    if (simple_clock && one_clock) {
        clock_root = dsu.find(bufg_outs.front());
        std::vector<std::pair<std::string, std::string>> kept;
        for (const auto &a : assigns)
            if (dsu.find(a.first) != clock_root) kept.push_back(a);
        if (kept.size() != assigns.size())
            std::cerr << "  dropped " << (assigns.size() - kept.size())
                      << " assign(s) onto the clock net\n";
        assigns.swap(kept);
    }

    // ---- port names from the XDC -----------------------------------------
    // The design already names its own boundary: PACKAGE_PIN ties a port to a
    // package pin, package_pins.csv ties that pin to an IOB site, and the site
    // pin `I`/`O` gives the wire the fabric sees.  Naming the ports after the
    // design rather than after a routing wire is what lets a comparison match
    // them without a hand-written map.
    std::map<std::string, std::string> friendly;   // net root -> XDC port name
    {
        int named = 0;
        for (const auto &[port, pin] : xdc_ports) {
            auto ps = pin_site.find(pin);
            if (ps == pin_site.end()) continue;
            const std::string &tile = ps->second.second, &site = ps->second.first;
            auto ti = tiles.find(tile);
            if (ti == tiles.end()) continue;
            load_type(ti->second.type);
            std::vector<std::string> ss;
            for (const auto &kv : ti->second.sites) ss.push_back(kv.first);
            std::sort(ss.begin(), ss.end(), [](const std::string &a, const std::string &b) {
                auto y = [](const std::string &n) { auto p = n.rfind('Y'); return p == std::string::npos ? 0 : atoi(n.c_str() + p + 1); };
                return y(a) < y(b);
            });
            int ordinal = int(std::find(ss.begin(), ss.end(), site) - ss.begin());
            const auto &per = site_pins[ti->second.type];
            if (ordinal >= int(per.size())) continue;
            // The IOB-site seed ("The pads, likewise") puts every pad's I and O
            // wires in the graph, so a naive label of both sides makes every
            // output-only pad look bidirectional and the split below takes the
            // XDC name off the side the design drives.  Direction comes from
            // the FASM: DRIVE/.OUT is an OBUF, .IN/.IN_ONLY an IBUF.  Label I
            // only when the site has an input buffer, and O only when it has
            // an output buffer.  A site with both is bidirectional and is
            // labelled on both sides, as before.
            //
            // FASM names the two sites of a full IOB tile by type, not by the
            // tile-type y_coord: IOB33M is IOB_Y0, IOB33S is IOB_Y1 (the same
            // rule fasmIobSuffix in netlist_core.cpp uses).  A *_SING tile has
            // one site; nextpnr writes IOB_Y1 above the HCLK row and IOB_Y0
            // below, while the type spells IOB_Y0 -- either spelling is that
            // site.  OUT_DIFF marks an OBUFDS: the S site is the N pad, whose
            // O is not a fabric net this comparison can name (it stays skipped).
            std::string site_type;
            for (const auto &kv : ti->second.sites)
                if (kv.first == site) { site_type = kv.second; break; }
            const bool site_is_m = !site_type.empty() && site_type.back() == 'M';
            const bool site_is_s = !site_type.empty() && site_type.back() == 'S';
            const bool single_iob_site = per.size() == 1;
            bool tile_out_diff = false;
            bool site_has_in = false, site_has_out = false;
            if (auto ot = dc.other_tiles.find(tile); ot != dc.other_tiles.end()) {
                std::string want;
                if (site_is_m) want = "IOB_Y0";
                else if (site_is_s) want = "IOB_Y1";
                else if (ordinal < int(site_names[ti->second.type].size()))
                    want = site_names[ti->second.type][ordinal];
                for (const auto &feat : ot->second) {
                    if (feat == "OUT_DIFF") tile_out_diff = true;
                    auto d1 = feat.find('.');
                    if (d1 == std::string::npos) continue;
                    std::string fasm_site = feat.substr(0, d1);
                    if (fasm_site.rfind("IOB_Y", 0) != 0) continue;
                    const bool names_this_site = (fasm_site == want);
                    const bool sing_spelling = single_iob_site;
                    if (!names_this_site && !sing_spelling) continue;
                    std::string rest = feat.substr(d1 + 1);
                    if (iob_feat_is_in(rest)) site_has_in = true;
                    if (iob_feat_is_out(rest)) site_has_out = true;
                }
            }
            const bool output_only = site_has_out && !site_has_in;
            const bool input_only = site_has_in && !site_has_out;
            const bool differential_n = tile_out_diff && site_is_s;
            for (const char *pn : {"I", "O"}) {
                auto it = per[ordinal].find(pn);
                if (it == per[ordinal].end()) continue;
                const bool receive_side = pn[0] == 'I';
                const bool skip_receive_of_output_only = receive_side && output_only;
                if (skip_receive_of_output_only) continue;
                const bool skip_drive_of_input_only = !receive_side && input_only;
                if (skip_drive_of_input_only) continue;
                const bool skip_obufds_n = !receive_side && differential_n;
                if (skip_obufds_n) continue;
                std::string ep = tw(tile, it->second);
                if (!dsu.parent.count(ep)) continue;
                friendly[dsu.find(ep)] = port;
                named++;
            }
        }
        if (!xdc_ports.empty())
            std::cerr << "  XDC: labelled " << named << " of " << xdc_ports.size() << " pads\n";
    }

    // The same three files that tell the equivalence checker which fabric net
    // is which register also let the dump be written in the designer's own
    // vocabulary.  A pad's XDC name wins where the two collide: a port name is
    // a fact about the board, a register name only about the synthesis.
    std::map<std::string, std::string> reg_label;   // tile/wire -> source signal
    if (!placement_path.empty() && !gold_json_path.empty()) {
        lvs::RegMap rm = lvs::build_regmap(placement_path, gold_json_path, db, device);
        reg_label = rm.net;
        int named = 0;
        for (const auto &kv : rm.net) {
            if (!dsu.parent.count(kv.first)) continue;
            std::string root = dsu.find(kv.first);
            if (friendly.count(root)) continue;
            friendly[root] = kv.second;
            named++;
        }
        std::cerr << "  placement: labelled " << named << " of " << rm.mapped << " registers\n";
    }

    // ---- I/O logic: the bypass between the fabric and a pad ---------------
    // A pad has an OLOGIC or ILOGIC site in the way, and a design that wants a
    // plain wire needs it to pass straight through.  Configuring nothing IS
    // that state: nextpnr's hp-diffio routes an input through an ILOGIC whose
    // site carries no bits at all, so keying this off the site's features
    // would miss it entirely.  What marks the site as used is the routing --
    // something drives D and something reads O -- so that is the test.
    //
    // The output half the database already declares hardwired as a
    // pseudo-PIP; the input half is in no database here.  Only what is
    // missing is added, or the net ends up with two drivers.
    {
        std::set<std::string> already;
        for (const auto &a : assigns)
            already.insert(a.first);
        // Pins a DDR register owns.  The database declares the site's output
        // bypass as a hardwired pseudo-PIP and it is applied to every site,
        // including the ones where a REGISTER drives the pin -- so the net
        // ends up with two drivers, the register and a wire straight past it,
        // and which one a reader believes is a coin toss.  Collected here and
        // filtered out below, once the loop has seen every site.
        std::set<std::string> ddr_driven;
        int bypassed = 0, unmodelled_io = 0, hardwired = 0;
        // The tiles to look at: every tile the FASM routes through, and
        // every tile whose I/O site it configures.  The second set is not a
        // subset of the first: an input-only IOI tile sets no routing bit --
        // pad to D is hardwired, O to the fabric a pseudo-PIP -- and appears
        // in a Vivado bitstream only through its site features.  nextpnr's
        // FASM names the tile anyway because it writes the pseudo-PIPs it
        // used; a bitstream cannot.
        std::map<std::string, std::vector<std::string>> io_tiles;
        for (const auto &tkv : dc.other_tiles) io_tiles[tkv.first];
        for (const auto &ikv : dc.iologic) {
            auto slash = ikv.first.find('/');
            if (slash != std::string::npos) io_tiles[ikv.first.substr(0, slash)];
        }
        for (const auto &tkv : io_tiles) {
            auto ti = tiles.find(tkv.first);
            if (ti == tiles.end()) continue;
            load_type(ti->second.type);
            for (const auto &pins : site_pins[ti->second.type]) {
                // ILOGIC receives on D (or DDLY, from the delay beside it) and
                // presents O; OLOGIC takes D1 and drives OQ; IDELAY takes
                // IDATAIN from the pad or DATAIN from the fabric and presents
                // DATAOUT.  A site with none of those pairs is not I/O logic.
                for (int kind = 0; kind < 3; kind++) {
                    const char *out_pin = kind == 0 ? "O" : kind == 1 ? "OQ" : "DATAOUT";
                    const char *tags[] = {"ILOGIC", "OLOGIC", "IDELAY"};
                    auto d = pins.find(out_pin);
                    if (d == pins.end()) continue;
                    const std::string &owire = d->second;
                    std::string tag = tags[kind];
                    auto at = owire.find(tag);
                    if (at == std::string::npos) continue;

                    // the site's FASM name carries the same index its wires do
                    std::string idx = owire.substr(at + tag.size(), 1);
                    // ...except in a _SING_ tile.  It holds ONE site of each
                    // kind and spells that site's wires with index 0 whichever
                    // half of a full tile it stands for, while the FASM names
                    // the site by the half: OLOGIC_Y1 in the SING above its
                    // HCLK row, OLOGIC_Y0 in the one below.  Going by the wire,
                    // the upper one's configuration is never found, and an
                    // OSERDESE2 there is extracted as the bypass wire past it.
                    // With one site of the kind there is no neighbour to take
                    // it for, so the half is whichever one the FASM configured.
                    const auto &type_sites = site_pins[ti->second.type];
                    const bool single_site =
                        std::count_if(type_sites.begin(), type_sites.end(), [&](const auto &s) {
                            auto p = s.find(out_pin);
                            return p != s.end() && p->second.find(tag) != std::string::npos;
                        }) == 1;
                    const bool configured_y0 = dc.iologic.count(tkv.first + "/" + tag + "_Y0") > 0;
                    const bool configured_y1 = dc.iologic.count(tkv.first + "/" + tag + "_Y1") > 0;
                    const bool fasm_names_one_half = configured_y0 != configured_y1;
                    if (single_site && fasm_names_one_half)
                        idx = configured_y1 ? "1" : "0";
                    auto cfg = dc.iologic.find(tkv.first + "/" + tag + "_Y" + idx);
                    // A DDR register is cut at its boundary and instantiated,
                    // the way a block RAM is: the checker treats the outputs as
                    // free and the inputs as obligations, so what is asserted is
                    // which net reaches which pin.  The synthesis side is cut on
                    // the same primitive with the same port names, so the two
                    // cuts cancel.  Modelling the two edges instead would put a
                    // negedge register into a proof with no notion of one.
                    if (cfg != dc.iologic.end() && cfg->second.is_ddr_block() &&
                        (kind == 0 || kind == 1)) {
                        static const char *iddr_ports[][2] = {
                            {"D", "D"}, {"C", "CLK"}, {"CE", "CE1"}, {"R", "SR"},
                            {"Q1", "Q1"}, {"Q2", "Q2"}, {nullptr, nullptr}};
                        static const char *oddr_ports[][2] = {
                            {"Q", "OQ"}, {"C", "CLK"}, {"CE", "OCE"}, {"R", "SR"},
                            {"D1", "D1"}, {"D2", "D2"}, {nullptr, nullptr}};
                        const bool in = (kind == 0);
                        DdrSite ds;
                        ds.tile = tkv.first;
                        ds.site = tag + "_Y" + idx;
                        ds.prim = in ? "IDDR" : "ODDR";
                        ds.iname = tkv.first + "_" + ds.site;
                        for (auto pp = in ? iddr_ports : oddr_ports; (*pp)[0]; pp++) {
                            const char *port = (*pp)[0];
                            std::string sitepin = (*pp)[1];
                            // The input mux may take the delayed tap instead.
                            if (in && sitepin == "D" && cfg->second.delayed_input)
                                sitepin = "DDLY";
                            auto q = pins.find(sitepin);
                            if (q == pins.end()) continue;
                            ds.ports.push_back({port, q->second});
                        }
                        // The site drives its outputs, so nothing else may.
                        for (const auto &pr : ds.ports)
                            if ((in && pr.first.rfind("Q", 0) == 0) ||
                                (!in && pr.first == "Q")) {
                                already.insert(tw(tkv.first, pr.second));
                                ddr_driven.insert(tw(tkv.first, pr.second));
                            }
                        ddr_sites.push_back(std::move(ds));

                        // An OLOGIC holds TWO registers, not one: the OUTFF on
                        // the data path and the TFF on the tristate path, each
                        // a separate ODDR cell in the synthesis.  Emit the
                        // second whenever the site says its T register is in
                        // use, or a bidirectional pad is short by one cell and
                        // everything the pad feeds reads as different.
                        // ...but IN_USE alone over-states it.  An
                        // output-only pad wears the bit too -- the SD clock
                        // does -- while its netlist holds no tristate cell at
                        // all, and emitting one there swaps a missing cell for
                        // a spurious one.  What separates the two is the
                        // routing: a real tristate has the fabric driving T1.
                        // On this design that test picks out exactly the five
                        // sites prjxray also marks ZINV_T1, which is the
                        // independent confirmation that it picks the right ones.
                        auto t1 = pins.find("T1");
                        const bool t_driven = t1 != pins.end() &&
                                              pip_driven.count(tw(tkv.first, t1->second));
                        if (!in && cfg->second.tddr_in_use && t_driven) {
                            static const char *tddr_ports[][2] = {
                                {"Q", "TQ"}, {"C", "CLK"}, {"CE", "TCE"},
                                {"R", "SR"}, {"D1", "T1"}, {"D2", "T2"},
                                {nullptr, nullptr}};
                            DdrSite ts;
                            ts.tile = tkv.first;
                            ts.site = tag + "_Y" + idx;
                            ts.prim = "ODDR";
                            // Two cells in one site need two names, and the
                            // suffix is the bel the placement already names.
                            ts.iname = tkv.first + "_" + ts.site + "_TFF";
                            for (auto pp = tddr_ports; (*pp)[0]; pp++) {
                                auto q = pins.find((*pp)[1]);
                                if (q == pins.end()) continue;
                                ts.ports.push_back({(*pp)[0], q->second});
                            }
                            for (const auto &pr : ts.ports)
                                if (pr.first == "Q") {
                                    already.insert(tw(tkv.first, pr.second));
                                    ddr_driven.insert(tw(tkv.first, pr.second));
                                }
                            ddr_sites.push_back(std::move(ts));
                        }
                        continue;
                    }
                    // A wide SERDES is cut at its boundary and instantiated as
                    // the primitive, exactly as a DDR register is: the outputs
                    // become free variables and the parallel inputs the
                    // obligations, and the synthesis carries the same
                    // OSERDESE2/ISERDESE2 with the same port names so the two
                    // cuts cancel.  (No SHIFTIN/SHIFTOUT cascade appears in any
                    // design here, so each is one cell with one boundary.)  An
                    // OSERDESE2 lives in the OLOGIC, an ISERDESE2 in the ILOGIC;
                    // IDELAY (kind 2) is a wire and handled below.
                    if (cfg != dc.iologic.end() && cfg->second.serdes_wide &&
                        (kind == 0 || kind == 1)) {
                        const bool in = (kind == 0);
                        // primitive port -> site pin.  RST arrives on the
                        // shared SR pin; the ISERDES data input takes the
                        // delayed tap when the mux says so, as an IDDR's does.
                        static const char *oser_ports[][2] = {
                            {"OQ", "OQ"}, {"TQ", "TQ"}, {"D1", "D1"}, {"D2", "D2"},
                            {"D3", "D3"}, {"D4", "D4"}, {"D5", "D5"}, {"D6", "D6"},
                            {"D7", "D7"}, {"D8", "D8"}, {"T1", "T1"}, {"T2", "T2"},
                            {"T3", "T3"}, {"T4", "T4"}, {"OCE", "OCE"}, {"TCE", "TCE"},
                            {"CLK", "CLK"}, {"CLKDIV", "CLKDIV"}, {"RST", "SR"},
                            {nullptr, nullptr}};
                        static const char *iser_ports[][2] = {
                            {"O", "O"}, {"Q1", "Q1"}, {"Q2", "Q2"}, {"Q3", "Q3"},
                            {"Q4", "Q4"}, {"Q5", "Q5"}, {"Q6", "Q6"}, {"Q7", "Q7"},
                            {"Q8", "Q8"}, {"D", "D"}, {"CE1", "CE1"}, {"CE2", "CE2"},
                            {"CLK", "CLK"}, {"CLKB", "CLKB"}, {"CLKDIV", "CLKDIV"},
                            {"RST", "SR"}, {"BITSLIP", "BITSLIP"}, {nullptr, nullptr}};
                        DdrSite ds;
                        ds.tile = tkv.first;
                        ds.site = tag + "_Y" + idx;
                        ds.prim = in ? "ISERDESE2" : "OSERDESE2";
                        ds.iname = tkv.first + "_" + ds.site;
                        for (auto pp = in ? iser_ports : oser_ports; (*pp)[0]; pp++) {
                            const char *port = (*pp)[0];
                            std::string sitepin = (*pp)[1];
                            if (in && sitepin == "D" && cfg->second.delayed_input)
                                sitepin = "DDLY";
                            auto q = pins.find(sitepin);
                            if (q == pins.end()) continue;
                            ds.ports.push_back({port, q->second});
                        }
                        // The site drives its outputs, so the bypass pseudo-PIP
                        // must not: OSERDESE2 drives OQ/TQ, ISERDESE2 O/Q1..Q8.
                        for (const auto &pr : ds.ports)
                            if (pr.first == "OQ" || pr.first == "TQ" ||
                                pr.first == "O" || pr.first.rfind("Q", 0) == 0) {
                                already.insert(tw(tkv.first, pr.second));
                                ddr_driven.insert(tw(tkv.first, pr.second));
                            }
                        ddr_sites.push_back(std::move(ds));
                        continue;
                    }
                    if (cfg != dc.iologic.end() && !cfg->second.is_bypass()) {
                        unmodelled_io++;
                        continue;
                    }

                    // Which input the site is passing through is a decoded
                    // fact, not a fixed pin: the ILOGIC mux may select the
                    // delayed input, and the delay may be fed from the pad or
                    // from the fabric.
                    const char *in_pin = kind == 0 ? "D" : kind == 1 ? "D1" : "IDATAIN";
                    if (cfg != dc.iologic.end()) {
                        if (kind == 0 && cfg->second.delayed_input) in_pin = "DDLY";
                        if (kind == 2 && !cfg->second.delay_from_pad) in_pin = "DATAIN";
                    }
                    auto sp = pins.find(in_pin);
                    if (sp == pins.end()) continue;

                    std::string dst = tw(tkv.first, owire), src = tw(tkv.first, sp->second);
                    if (already.count(dst)) { hardwired++; continue; }
                    if (!already.count(src)) continue;   // nothing drives it: unused
                    assigns.push_back({dst, src});
                    already.insert(dst);
                    bypassed++;
                }
            }
        }
        if (bypassed || hardwired || unmodelled_io) {
            std::cerr << "  I/O logic: " << bypassed << " pass-through added, " << hardwired
                      << " already hardwired";
            if (!ddr_sites.empty())
                std::cerr << ", " << ddr_sites.size() << " DDR cut at their boundary";
            if (unmodelled_io)
                std::cerr << ", " << unmodelled_io << " doing more than a wire (not modelled)";
            std::cerr << "\n";
        }
        if (!ddr_driven.empty()) {
            std::vector<std::pair<std::string, std::string>> kept;
            for (const auto &a : assigns)
                if (!ddr_driven.count(a.first)) kept.push_back(a);
            if (kept.size() != assigns.size())
                std::cerr << "  dropped " << (assigns.size() - kept.size())
                          << " bypass assign(s) onto a pin a DDR register drives\n";
            assigns.swap(kept);
        }
    }

    // One place decides how a net is written: its XDC name where it has one,
    // otherwise the sanitised (tile, wire).  Used by the declarations, the
    // routing assigns and the instance pins alike -- writing a net one way in
    // one place and another way elsewhere silently splits it in two.
    // A column carries a cell of the source design where one was placed on
    // its flip-flop; naming the instance after that cell makes the dump
    // readable.  The suffix keeps the instance out of the net namespace.
    // A column is named after the register it holds.  The placement and the
    // emitter disagree about what to call a site -- one names it absolutely
    // (SLICE_X0Y100), the other by its position in the tile -- but they agree
    // about wires, so the column's output endpoints are what they match on:
    // the main flip-flop leaves on xQ, the second one on xMUX.
    auto inst_name = [&](const std::string &tile, const std::string &site, const std::string &col,
                         const std::string &q, const std::string &mux) {
        for (const std::string &ep : {q, mux}) {
            auto it = reg_label.find(ep);
            if (it != reg_label.end()) return it->second + "_i";
        }
        return sanitise(tile + "_" + site + "_" + col);
    };

    auto emit_net = [&](const std::string &endpoint) {
        std::string root = dsu.find(endpoint);
        auto f = friendly.find(root);
        return f == friendly.end() ? sanitise(root) : ("\\" + f->second + " ");
    };

    // ---- emit ------------------------------------------------------------
    std::ofstream fout;
    std::ostream &os = out_path.empty() ? std::cout : (fout.open(out_path), fout);

    os << "// Generated by tileverilog: one instance per occupied slice, one\n"
          "// assign per routing feature.  All device knowledge is in xclb below.\n";
    if (timing) os << "`timescale 1ns/1ps\n";
    os << "`default_nettype none\n\n";

    std::ofstream mfout;
    std::ostream &ms = model_path.empty() ? os : (mfout.open(model_path), mfout);
    if (timing) ms << "`timescale 1ns/1ps\n`define XCOL_TIMING\n";
    ms << R"(// ---- the tile model: one CLB column, four to a slice --------------------
// O6 is the 6-input read of INIT; O5 is the low half, i.e. the same read with
// A6 held low.  FF_SRC / FF5_SRC / OUTMUX are the decoded selects; the values
// this model does not implement resolve to 0 and are reported by the emitter.
module xcol #(
    parameter [63:0] INIT = 64'h0,
    parameter RAM     = 0,        // 1 = the LUT storage is writable
    parameter RAM32   = 0,        // 1 = two 32-deep halves rather than one 64
    parameter FF_SRC  = "none",   // O6 | O5 | X | XOR | CY | F7F8 | none
    parameter FF5_SRC = "none",   // O5 | X | none
    parameter OUTMUX  = "none",   // O6 | O5 | 5Q | XOR | CY | F7 | F8 | none
    parameter CY0     = "X",      // the carry mux data input: O5 or the X bypass
    parameter FF_INIT = 1'b0, parameter FF_SRVAL = 1'b0,
    parameter FF5_INIT = 1'b0, parameter FF5_SRVAL = 1'b0,
    parameter SYNC = 1'b1,
    parameter FF_THRU = 1'b0,     // the main register is a latch held open: Q = D
    // A column of a deeper distributed RAM.  A 128- or 256-deep single-port
    // RAM spans two or four columns of one slice: each holds 64 of the words,
    // the write goes to the one column WA7/WA8 select, and the read is the
    // slice's F7/F8 mux tree over the columns' O6, steered by the same two
    // bits on the bypass pins.  The tile model still writes every column of
    // the group -- it has no per-column write decode -- and reads them
    // through the mux it builds between them, which is the wrong memory
    // and the right boundary: the equivalence check cuts the group at its
    // mux output (GOUT), so what it compares is the address, data and
    // enable that reach the group, never the words inside it.
    parameter DEPTH = 64,         // 64 | 128 | 256
    parameter GROUP = "",         // the group this column belongs to, if DEPTH > 64
    parameter GOUT  = ""          // the net the group reads out on: its F7 or F8
) (
    input  wire A1, A2, A3, A4, A5, A6, X,
    input  wire RA7, RA8,         // the group's read address above A6: the F7 and F8 selects
    input  wire WA7, WA8,         // ...and its write address above WA[5:0]: CX and BX
    // The wide multiplexer that reaches this column.  It is built OUTSIDE the
    // column, from two neighbouring columns' O6 and one of the slice's bypass
    // pins, because that is where it physically is -- a column cannot see its
    // neighbour's LUT, and pretending otherwise here would put the wiring in
    // the one place that cannot get it right.
    input  wire FX,
    input  wire CLK, CE, SR, CI,
    input  wire [5:0] WA,         // write address, shared by the whole slice
    input  wire DI, DI2, WE,      // write data (DI2 = the upper half when 32-deep)
    output wire O6, O5, Q, MUX, CO
);
    wire [5:0] idx6 = {A6, A5, A4, A3, A2, A1};
    wire [5:0] idx5 = {1'b0, A5, A4, A3, A2, A1};

    // Distributed RAM is this same storage made writable: the read path is
    // unchanged -- it IS the LUT read -- so the only new behaviour is a write
    // port, and a column with RAM=0 reduces to exactly the constant it was.
    //
    // 64 deep: one memory, written at WA from DI.
    // 32 deep: TWO memories in the one LUT, each five bits deep.  The low half
    // is what O5 reads and the high half what O6 reads with A6 high, so they
    // take separate write data -- DI and DI2 -- at the same address.  Treating
    // this as one 64-deep memory with a six-bit address would write one half
    // and leave the other holding its initial contents for ever.
    reg [63:0] mem = INIT;
    always @(posedge CLK)
        if (RAM && WE) begin
            if (RAM32) begin
                mem[{1'b0, WA[4:0]}] <= DI;
                mem[{1'b1, WA[4:0]}] <= DI2;
            end else begin
                mem[WA] <= DI;
            end
        end

    assign O6 = mem[idx6];
    assign O5 = mem[idx5];

    // CARRY4, one bit of it: O6 is the propagate select, and the data input
    // is O5 or the bypass depending on CY0.  CO ripples to the next column,
    // and the XOR output is the sum bit.
    wire di  = (CY0 == "O5") ? O5 : X;
    assign CO = O6 ? CI : di;
    wire xo  = O6 ^ CI;

    wire ff_d  = (FF_SRC  == "O6")  ? O6 : (FF_SRC  == "O5") ? O5 :
                 (FF_SRC  == "X")   ? X  : (FF_SRC  == "XOR") ? xo :
                 (FF_SRC  == "CY")  ? CO : (FF_SRC == "F7F8") ? FX : 1'b0;
    wire ff5_d = (FF5_SRC == "O5") ? O5 : (FF5_SRC == "X")  ? X  : 1'b0;

    reg q = FF_INIT, q5 = FF5_INIT;
    always @(posedge CLK)
        if (SYNC) begin
            if (SR) q <= FF_SRVAL; else if (CE) q <= ff_d;
        end else begin
            if (CE) q <= ff_d;
        end
    always @(posedge CLK)
        if (SYNC) begin
            if (SR) q5 <= FF5_SRVAL; else if (CE) q5 <= ff5_d;
        end else begin
            if (CE) q5 <= ff5_d;
        end

    assign Q   = FF_THRU ? ff_d : q;
    assign MUX = (OUTMUX == "O6")  ? O6 : (OUTMUX == "O5") ? O5 :
                 (OUTMUX == "5Q")  ? q5 : (OUTMUX == "XOR") ? xo :
                 (OUTMUX == "CY")  ? CO :
                 (OUTMUX == "F7" || OUTMUX == "F8") ? FX : 1'b0;
`ifdef XCOL_TIMING
    // The slice's arcs, from the Vivado library as Project X-Ray's SDF
    // records them (timings/CLBLM_L.sdf: FF_INIT, LUT6): fast_min : slow_max.
    // The register's D is internal, so its setup and hold are checked at the
    // pins that reach it, only on a column that has a register.
    wire has_ff = (FF_SRC != "none") || (FF5_SRC != "none");
    specify
        (A1 => O6) = (0.045:0.124:0.124);  (A1 => O5) = (0.045:0.124:0.124);
        (A2 => O6) = (0.045:0.124:0.124);  (A2 => O5) = (0.045:0.124:0.124);
        (A3 => O6) = (0.045:0.124:0.124);  (A3 => O5) = (0.045:0.124:0.124);
        (A4 => O6) = (0.045:0.124:0.124);  (A4 => O5) = (0.045:0.124:0.124);
        (A5 => O6) = (0.045:0.124:0.124);  (A5 => O5) = (0.045:0.124:0.124);
        (A6 => O6) = (0.045:0.124:0.124);
        (A1 => MUX) = (0.045:0.124:0.124); (A2 => MUX) = (0.045:0.124:0.124);
        (A3 => MUX) = (0.045:0.124:0.124); (A4 => MUX) = (0.045:0.124:0.124);
        (A5 => MUX) = (0.045:0.124:0.124); (A6 => MUX) = (0.045:0.124:0.124);
        (X => MUX) = (0.030:0.080:0.080);  (CI => CO) = (0.020:0.050:0.050);
        (posedge CLK => (Q : ff_d)) = (0.099:0.303:0.303);
        (posedge CLK => (MUX : q5)) = (0.099:0.303:0.303);
        $setuphold(posedge CLK &&& has_ff, A1, -0.057:-0.046:-0.046, 0.181:0.225:0.225);
        $setuphold(posedge CLK &&& has_ff, A2, -0.057:-0.046:-0.046, 0.181:0.225:0.225);
        $setuphold(posedge CLK &&& has_ff, A3, -0.057:-0.046:-0.046, 0.181:0.225:0.225);
        $setuphold(posedge CLK &&& has_ff, A4, -0.057:-0.046:-0.046, 0.181:0.225:0.225);
        $setuphold(posedge CLK &&& has_ff, A5, -0.057:-0.046:-0.046, 0.181:0.225:0.225);
        $setuphold(posedge CLK &&& has_ff, A6, -0.057:-0.046:-0.046, 0.181:0.225:0.225);
        $setuphold(posedge CLK &&& has_ff, X,  -0.057:-0.046:-0.046, 0.181:0.225:0.225);
        $setuphold(posedge CLK &&& has_ff, CE,  0.088:0.109:0.109, -0.011:-0.009:-0.009);
        $setuphold(posedge CLK &&& has_ff, SR,  0.088:0.109:0.109, -0.011:-0.009:-0.009);
    endspecify
`endif
endmodule

)";
    if (!model_path.empty())
        os << "// tile model written separately to " << model_path << "\n\n";

    // A net nothing in this design drives is something outside it drives: a
    // pad, a clock arriving from a tile we do not model.  Those become module
    // inputs, which is what makes the result simulatable at all.
    // Record raw endpoints, not resolved roots: resolving a slice's pins can
    // merge nets further on, and a root taken too early goes stale.
    std::set<std::string> driven_raw;
    for (const auto &a : assigns) driven_raw.insert(a.first);

    // slice instances (built first: slice outputs count as driven)
    std::ostringstream body;
    std::vector<std::string> carry_wires;
    // Nets this model invents rather than reads out of the fabric: the outputs
    // of a slice's wide multiplexers and of a block RAM's pin inverters.
    std::vector<std::string> helper_wires;
    std::vector<std::pair<std::string, std::string>> carry_assigns;
    int inst = 0, unmodelled = 0;
    // The nets the routing reads from, by root -- taken here, after the last
    // union, since a root recorded earlier may since have been merged away.
    std::set<std::string> read_roots;
    for (const auto &w : real_pip_sources) read_roots.insert(dsu.find(w));
    for (const auto &kv : dc.slices) {
        const SliceConfig &sc = kv.second;
        auto ti = tiles.find(sc.tile);
        if (ti == tiles.end()) continue;
        int ordinal = sc.site.back() - '0';
        const auto &per = site_pins[ti->second.type];
        if (ordinal >= int(per.size())) continue;
        const auto &pins = per[ordinal];
        auto raw = [&](const std::string &pin) -> std::string {
            auto it = pins.find(pin);
            return it == pins.end() ? std::string() : tw(sc.tile, it->second);
        };
        auto net = [&](const std::string &pin) -> std::string {
            std::string r = raw(pin);
            if (r.empty()) return "1'b0";
            return emit_net(r);
        };
        unmodelled += int(sc.unhandled.size());

        // The carry chain runs A -> B -> C -> D and on to the slice above.
        // Its start comes from PRECYINIT; its end drives the COUT site pin,
        // which tileconn joins to the CIN of the slice above.
        std::string prefix = sanitise(sc.tile + "_" + sc.site);
        // There is no "CARRY4 in use" bit.  CARRY4.<col>CY0 says a column's
        // carry data comes from O5, and that was the only evidence looked
        // for -- enough for nextpnr, whose adders take DI from the LUT's O5,
        // and wrong for Vivado, which feeds a constant DI through the X
        // bypass (a tie-off on AX..DX), leaving no CY0 feature at all.  With
        // the chain not instantiated every CI is zero and the XOR sum bit
        // collapses to O6: an incrementer that never increments, quietly.
        // So take the chain to exist on any sign of use: a CY0, a column
        // reading the XOR or CY into its flip-flop or output mux, a start
        // other than the idle zero, or a COUT that the routing carries on.
        bool has_carry = false;
        for (const auto &cc : sc.columns) {
            const ColumnConfig &col = cc.second;
            has_carry |= col.carry_used;
            has_carry |= col.ff_used && col.ff_src_explicit &&
                         (col.ff_src == FFSrc::Xor || col.ff_src == FFSrc::Carry);
            has_carry |= col.outmux == OutMux::Xor || col.outmux == OutMux::Carry;
        }
        has_carry |= sc.precyinit == PreCyInit::One || sc.precyinit == PreCyInit::AX ||
                     sc.precyinit == PreCyInit::CIN;
        // COUT reaches the slice above through tileconn, not a PIP, so the
        // only sign that it is used is that slice starting its own chain
        // from CIN -- and a chain that is missing below it would hand it an
        // undriven carry-in.
        {
            auto y_at = sc.tile.rfind('Y');
            if (y_at != std::string::npos) {
                std::string above = sc.tile.substr(0, y_at + 1) +
                                    std::to_string(atoi(sc.tile.c_str() + y_at + 1) + 1);
                auto up = dc.slices.find(above + "/" + sc.site);
                if (up != dc.slices.end() && up->second.precyinit == PreCyInit::CIN)
                    has_carry = true;
            }
        }
        std::map<char, std::string> ci_of, co_of;
        if (has_carry) {
            std::string start;
            switch (sc.precyinit) {
            case PreCyInit::Zero: start = "1'b0"; break;
            case PreCyInit::One:  start = "1'b1"; break;
            case PreCyInit::AX:   start = net("AX"); break;
            case PreCyInit::CIN:  start = net("CIN"); break;
            default:              start = "1'b0"; break;
            }
            std::string prev = start;
            for (char c : {'A', 'B', 'C', 'D'}) {
                std::string co = prefix + "_CO_" + c;
                carry_wires.push_back(co);
                ci_of[c] = prev;
                co_of[c] = co;
                prev = co;
            }
            std::string cout_pin = net("COUT");
            if (cout_pin != "1'b0") carry_assigns.push_back({cout_pin, co_of['D']});
        }

        // The wide multiplexers.  A SLICE has two MUXF7s and one MUXF8, and
        // which LUTs and which bypass pin each one uses is not a guess: it is
        // what nextpnr's own packer builds (himbaechel/uarch/xilinx, pack.cc
        // constrain_muxf_tree and xilinx_place.cc).  There, I1's driver stays
        // in the same eight and I0's sits one spacing up, and the select is
        // the X input of the eight the mux is charged to:
        //
        //   F7A = AX ? A.O6 : B.O6     reaches column A
        //   F7B = CX ? C.O6 : D.O6     reaches column C
        //   F8  = BX ? F7A  : F7B      reaches column B
        //
        // Built here rather than inside `xcol` because it spans columns, and
        // emitted as MUXF7/MUXF8 cells so that both sides of a comparison
        // describe it with the same primitive.  Only built where a column
        // actually selects it -- there is no feature saying a mux exists, only
        // features saying a column reads one.
        std::map<char, std::string> fx_of;
        {
            auto selects_wide = [&](char c) {
                auto it = sc.columns.find(c);
                if (it == sc.columns.end()) return false;
                const ColumnConfig &cc = it->second;
                return cc.outmux == OutMux::F7 || cc.outmux == OutMux::F8 ||
                       (cc.ff_used && cc.ff_src == FFSrc::Wide);
            };
            bool need_a = selects_wide('A'), need_c = selects_wide('C'),
                 need_b = selects_wide('B');
            // An F8 is a mux of the two F7s, so wanting it wants them both.
            if (need_b) need_a = need_c = true;
            auto mk = [&](const std::string &name, const std::string &type,
                          const std::string &i0, const std::string &i1, const std::string &sel) {
                std::string w = prefix + "_" + name;
                helper_wires.push_back(w);
                body << "  " << type << " \\" << w << "_m (.I0(" << i0 << "), .I1(" << i1
                     << "), .S(" << sel << "), .O(" << w << "));\n";
                return w;
            };
            std::string f7a, f7b;
            if (need_a) f7a = mk("F7A", "MUXF7", net("B"), net("A"), net("AX"));
            if (need_c) f7b = mk("F7B", "MUXF7", net("D"), net("C"), net("CX"));
            if (need_a) fx_of['A'] = f7a;
            if (need_c) fx_of['C'] = f7b;
            if (need_b) fx_of['B'] = mk("F8", "MUXF8", f7b, f7a, net("BX"));
        }

        // A column with no feature at all -- no INIT, no register, no mux --
        // is absent from the decode, yet may still be a constant-0 LUT the
        // routing reads (the case explained below).  Bring such columns in
        // with a default configuration, so the loop sees them.
        std::map<char, ColumnConfig> columns = sc.columns;
        for (char c : {'A', 'B', 'C', 'D'}) {
            if (columns.count(c)) continue;
            std::string o6 = raw(std::string(1, c));
            if (!o6.empty() && read_roots.count(dsu.find(o6))) {
                ColumnConfig cc;
                cc.col = c;
                columns[c] = cc;
            }
        }
        for (const auto &cc : columns) {
            char c = cc.first;
            const ColumnConfig &col = cc.second;
            // A column with nothing configured is empty -- but "no INIT" is
            // not "nothing".  prjxray's bit2fasm omits a feature whose bits
            // are all zero, so a Vivado bitstream's RAM column with zero
            // initial contents (most of them) arrives with no INIT at all,
            // and dropping it silently deletes a quarter of a RAM32M.  A
            // writable column is live by definition, INIT or not.
            // The other face of the same gap: a LUT whose INIT is all zero
            // is how Vivado makes a constant 0, and bit2fasm writes nothing
            // for it.  What says the column is there is that the routing
            // reads its output -- so a column whose O6 feeds a PIP is kept,
            // INIT or not, and reads as the constant its (absent) INIT says.
            bool o6_read = false;
            {
                std::string o6 = raw(std::string(1, c));
                if (!o6.empty() && read_roots.count(dsu.find(o6))) o6_read = true;
            }
            if (!col.init && !col.ram && !o6_read && !col.ff_used && !col.ff5_used && col.outmux == OutMux::None) continue;
            std::string C(1, c);
            // Distributed RAM.  The write address is one per SLICE, not one
            // per column -- it arrives on the slice's WA pins, which the D
            // column's address inputs drive -- so every column of a memory
            // writes at the same place while each reads at its own.  The
            // write data is per column, chosen by that column's DI1 mux;
            // DI2 is the second datum the 32-deep mode needs, and it is the
            // column's X bypass pin.
            std::string wa = "6'b0", di = "1'b0", di2 = "1'b0", we = "1'b0";
            if (col.ram) {
                std::string w;
                for (int i = 6; i >= 1; i--) w += (i < 6 ? ", " : "") + net("D" + std::to_string(i));
                wa = "{" + w + "}";
                // The DI1 mux is a CHAIN, not a per-column choice: a column
                // with no DI1MUX feature of its own does not fall back to the
                // shared DI pin, it takes whatever the column below resolved
                // to.  A takes AI, or failing that B's choice; B takes BI or
                // DI; C takes CI or DI; D always takes DI.  Reading it as a
                // per-column default writes column A from the wrong pin
                // whenever B is the one holding the write data.
                auto di_of = [&](char x) {
                    auto own = [&](char y) {
                        auto it = sc.columns.find(y);
                        return it != sc.columns.end() && it->second.di1 == Di1Src::OwnI;
                    };
                    if (x == 'A') return own('A') ? net("AI") : own('B') ? net("BI") : net("DI");
                    if (x == 'B') return own('B') ? net("BI") : net("DI");
                    if (x == 'C') return own('C') ? net("CI") : net("DI");
                    return net("DI");
                };
                di = di_of(c);
                di2 = net(C + "X");
                we = sc.we_from_ce ? net("CE") : net("WE");
            }
            const char *ffsrc = col.ff_used ? (col.ff_src_explicit ? to_string(col.ff_src) : "O6") : "none";
            const char *ff5src = col.ff5_used ? (col.ff5_src_explicit ? to_string(col.ff5_src) : "O5") : "none";
            // A deeper single-port RAM: WA8USED says 256 over all four
            // columns, WA7USED 128 over a pair -- C/D when A is not a RAM,
            // else both pairs.  The group reads out on the mux the tree
            // above built for it.  (A 128x1D dual-port also sets WA7USED
            // with all four columns writable, reading its second port on
            // F7A; it is grouped the same way and reads out the same way.)
            int depth = 64;
            std::string group, gout;
            if (col.ram && !col.ram_small && (sc.wa8used || sc.wa7used)) {
                auto ram_col = [&](char x) {
                    auto it = sc.columns.find(x);
                    return it != sc.columns.end() && it->second.ram;
                };
                if (sc.wa8used) {
                    depth = 256;
                    group = prefix + "_M256";
                    gout = fx_of.count('B') ? fx_of['B'] : "";
                } else {
                    depth = 128;
                    bool cd = (c == 'C' || c == 'D') || !ram_col('A');
                    group = prefix + (cd ? "_M128CD" : "_M128AB");
                    gout = cd ? (fx_of.count('C') ? fx_of['C'] : "") : (fx_of.count('A') ? fx_of['A'] : "");
                }
            }
            // A slice in LATCH mode with its clock pin left unrouted is
            // Vivado's second way out of a column: BMUX carries the carry-out
            // and the XOR sum leaves through BQ, via a latch that is never
            // closed.  The unrouted pin reads the interconnect pull-up (the
            // database's own default, FAN_ALT -> VCC_WIRE), CLKINV turns that
            // into a low gate, and a 7-series slice latch is open on a low
            // gate -- which is the reading under which Vivado's own output
            // is a route-through and under no other.  A LATCH slice whose
            // clock IS routed is a real latch, which no boolean cone can
            // state; it is left as a register and reported.
            bool ff_thru = false;
            if (sc.latch && col.ff_used) {
                std::string clk_raw = raw("CLK");
                bool routed = false;
                if (!clk_raw.empty()) {
                    std::string root = dsu.find(clk_raw);
                    for (const auto &w : real_pip_driven)
                        if (dsu.find(w) == root) { routed = true; break; }
                }
                if (!routed && ((pullup ^ (sc.clkinv ? 1 : 0)) == 0))
                    ff_thru = true;
                else
                    unmodelled++;
            }
            std::ostringstream initv;
            initv << "64'h" << std::hex << (col.init ? *col.init : 0);
            body << "  xcol #(." << "INIT(" << initv.str() << "), .RAM(" << (col.ram ? 1 : 0)
               << "), .RAM32(" << (col.ram && col.ram_small ? 1 : 0) << "), .FF_SRC(\"" << ffsrc
               << "\"), .FF5_SRC(\"" << ff5src << "\"), .OUTMUX(\"" << to_string(col.outmux)
               << "\"), .CY0(\"" << (col.cy0_o5 ? "O5" : "X") << "\"),\n"
               << "        .FF_INIT(1'b" << col.ff_init << "), .FF_SRVAL(1'b" << col.ff_srval
               << "), .FF5_INIT(1'b" << col.ff5_init << "), .FF5_SRVAL(1'b" << col.ff5_srval
               << "), .SYNC(1'b" << (sc.ffsync ? 1 : 0) << "), .FF_THRU(1'b" << (ff_thru ? 1 : 0)
               << "), .DEPTH(" << depth << "), .GROUP(\"" << group << "\"), .GOUT(\"" << gout << "\"))\n"
               << "    \\" << inst_name(sc.tile, sc.site, C, raw(C + "Q"), raw(C + "MUX")) << " (";
            for (int i = 1; i <= 6; i++) body << ".A" << i << "(" << net(C + std::to_string(i)) << "), ";
            if (depth > 64) {
                // The read select of this column's own F7 is the X pin of the
                // pair's lower column (AX for A/B, CX for C/D); the F8's is BX.
                bool cd = (c == 'C' || c == 'D');
                body << ".RA7(" << net(cd ? "CX" : "AX") << "), .RA8(" << (depth == 256 ? net("BX") : std::string("1'b0"))
                     << "), .WA7(" << net("CX") << "), .WA8(" << (depth == 256 ? net("BX") : std::string("1'b0")) << "), ";
            } else {
                body << ".RA7(1'b0), .RA8(1'b0), .WA7(1'b0), .WA8(1'b0), ";
            }
            body << ".X(" << net(C + "X") << "), .CLK(" << net("CLK") << "), "
               << ".CE(" << (sc.ceusedmux ? net("CE") : std::string("1'b1")) << "), "
               << ".SR(" << (sc.srusedmux ? net("SR") : std::string("1'b0")) << "),\n"
               // O6 leaves the slice on the column's own site pin (A..D); O5
               // has no pin of its own -- it reaches the world through the 5FF
               // or the xMUX, both of which are wired below.
               // The carry into this column: the previous column's CO, or
               // whatever PRECYINIT selected at the bottom of the slice.  A
               // column outside a chain still has the pin, tied low, because
               // the model's XOR and CY paths read it unconditionally.
               << ".CI(" << (ci_of.count(c) ? ci_of[c] : std::string("1'b0")) << "), "
               << ".FX(" << (fx_of.count(c) ? fx_of[c] : std::string("1'b0")) << "),\n"
               << "     .WA(" << wa << "), .DI(" << di << "), .DI2(" << di2 << "), .WE(" << we << "),\n"
               << "     .O6(" << net(C) << "), .O5(), .Q(" << net(C + "Q")
               << "), .MUX(" << net(C + "MUX") << "), .CO("
               << (co_of.count(c) ? co_of[c] : std::string()) << "));\n";
            if (!raw(C).empty()) driven_raw.insert(raw(C));
            if (!raw(C + "Q").empty()) driven_raw.insert(raw(C + "Q"));
            if (!raw(C + "MUX").empty()) driven_raw.insert(raw(C + "MUX"));
            inst++;
        }
    }

    // A block RAM's contents, as instance parameters.  The FASM gives each
    // 18Kb half's rows as 256-bit literals; a 36Kb cell's rows are the two
    // halves' rows interleaved bit by bit, the lower half supplying the even
    // bits of each output row (the inverse of how Vivado splits a RAMB36E1
    // across them).  Rows that are all zero are left out: that is the
    // primitive's own default, so the parameter list stays readable and the
    // meaning is unchanged.
    auto fasm_row = [&](const std::string &tile, const std::string &site, const char *kind,
                        int idx) -> std::string {
        char key[64];
        snprintf(key, sizeof(key), "%s.%s_%02X[255:0]", site.c_str(), kind, idx);
        auto tv = dc.other_values.find(tile);
        if (tv == dc.other_values.end()) return std::string(256, '0');
        auto it = tv->second.find(key);
        if (it == tv->second.end()) return std::string(256, '0');
        // "256'b0101..." -- keep the bits, left-padded to the full row
        const std::string &v = it->second;
        size_t b = v.find('b');
        std::string bits = b == std::string::npos ? v : v.substr(b + 1);
        bits.erase(std::remove(bits.begin(), bits.end(), '_'), bits.end());
        if (bits.size() < 256) bits.insert(0, 256 - bits.size(), '0');
        return bits;
    };
    auto hex_of = [](const std::string &bits) {
        std::string out;
        for (size_t i = 0; i < bits.size(); i += 4) {
            int v = 0;
            for (int k = 0; k < 4; k++) v = (v << 1) | (bits[i + k] == '1' ? 1 : 0);
            out += "0123456789abcdef"[v];
        }
        size_t nz = out.find_first_not_of('0');
        return nz == std::string::npos ? std::string("0") : out.substr(nz);
    };
    auto content_params = [&](const BramSite &b) {
        std::vector<std::string> ps;
        auto add = [&](const char *kind, int idx, const std::string &bits) {
            if (bits.find('1') == std::string::npos) return;
            char key[32];
            snprintf(key, sizeof(key), "%s_%02X", kind, idx);
            ps.push_back(std::string(".") + key + "(256'h" + hex_of(bits) + ")");
        };
        auto build = [&](const char *kind, int rows) {
            for (int i = 0; i < rows; i++) {
                if (!b.is36) {
                    add(kind, i, fasm_row(b.tile, b.cfg_site, kind, i));
                    continue;
                }
                // 36Kb: interleave the halves into two rows of the whole cell
                std::string lo = fasm_row(b.tile, "RAMB18_Y0", kind, i);
                std::string hi = fasm_row(b.tile, "RAMB18_Y1", kind, i);
                std::string r0(256, '0'), r1(256, '0');
                for (int k = 0; k < 128; k++) {
                    r0[255 - 2 * k] = lo[255 - k];
                    r0[255 - (2 * k + 1)] = hi[255 - k];
                    r1[255 - 2 * k] = lo[255 - (128 + k)];
                    r1[255 - (2 * k + 1)] = hi[255 - (128 + k)];
                }
                add(kind, i * 2, r0);
                add(kind, i * 2 + 1, r1);
            }
        };
        build("INIT", b.is36 ? 0x40 : 0x40);
        build("INITP", 8);
        return ps;
    };

    // ---- block RAM: the boundary, and now the contents --------------------
    // A RAMB18E1 or RAMB36E1 is instantiated here with nothing inside it, and
    // that is the whole point.  The checker treats a memory's data outputs as
    // free variables and every one of its inputs as an obligation, so what has
    // to be right is the BOUNDARY -- which net reaches which pin -- and not
    // the contents.  The synthesis side is cut in the same place, on the same
    // primitive with the same port names, which is what lets the two cuts
    // cancel and the cones downstream of a ROM become comparable at all.
    //
    // What this does NOT check is the initial contents.  Two block RAMs with
    // identical boundaries and different INIT strings pass here.  That is a
    // real gap and it is deliberate: `fasm2netlist` reads the contents out of
    // the bitstream, and tests/rtl/build_and_check.py compares them.
    int brams = 0, bram_rows = 0;
    for (const auto &b : bram_sites) {
        if (b.canon.empty()) continue;
        // prjxray stores an inversion complemented, so the pins to invert are
        // the ones with no ZINV tag.
        std::set<std::string> inverted;
        {
            auto tfi = site_feats.find(b.tile);
            if (tfi != site_feats.end()) {
                auto cf = tfi->second.find(b.cfg_site);
                if (cf != tfi->second.end())
                    for (const char *pin : bram::kInvertible)
                        if (std::find(cf->second.begin(), cf->second.end(),
                                      "ZINV_" + std::string(pin)) == cf->second.end())
                            inverted.insert(pin);
            }
        }
        std::string iname = sanitise(b.tile + "_" + b.site);
        std::ostringstream o;
        bool first = true;

        // One port of the primitive.  `base` is the site pin its bit 0 sits
        // on; `baseU` the upper 18Kb half's copy, which exists only on the
        // 36Kb site and which in 36Kb mode carries the same signal.
        auto wire_up = [&](const char *port, int width, bool out, const bram::Port36 *p36,
                           const std::string &base) {
            int n = width ? width : 1;
            std::vector<std::string> bits;   // MSB first, as a concatenation is written
            bool any = false;
            for (int i = n - 1; i >= 0; i--) {
                std::string suffix = width ? std::to_string(i) : std::string();
                std::string bit;
                std::vector<std::string> sps;
                if (p36) {
                    auto [l, u] = bram::pins36(*p36, i);
                    sps.push_back(l);
                    if (!u.empty()) sps.push_back(u);
                } else {
                    sps.push_back(base + suffix);
                }
                for (const auto &sp : sps) {
                    auto it = b.canon.find(sp);
                    if (it == b.canon.end()) continue;
                    std::string raw = tw(b.tile, it->second);
                    if (out) driven_raw.insert(raw);
                    // Referencing the endpoint is what puts an unrouted pin on
                    // the interconnect pull-up, the same as every other net
                    // the design leaves alone.
                    std::string nm = emit_net(raw);
                    if (bit.empty()) bit = nm;
                }
                if (!bit.empty()) any = true;
                bits.push_back(bit.empty() ? "1'b0" : bit);
            }
            if (!any) return;
            // An inverted control pin gets a real inverter rather than a note
            // in a parameter, because what a boundary compares is the value
            // the site SEES.  The synthesis says the same thing the other way
            // round, as IS_<pin>_INVERTED, and src/lvs/cone.cpp applies it
            // there so that the two descriptions meet.  Every invertible pin
            // is a scalar, so there is no bus case to get wrong.
            if (!width && inverted.count(port)) {
                std::string w = iname + "_" + port + "_inv";
                helper_wires.push_back(w);
                body << "  INV \\" << w << "_i (.I(" << bits[0] << "), .O(" << w << "));\n";
                bits[0] = w;
            }
            o << (first ? "" : ", ") << "." << port << "(";
            first = false;
            if (width) {
                o << "{";
                for (size_t i = 0; i < bits.size(); i++) o << (i ? ", " : "") << bits[i];
                o << "}";
            } else {
                o << bits[0];
            }
            o << ")";
        };

        if (b.is36)
            for (const auto &p : bram::kRamb36) wire_up(p.port, p.width, p.out, &p, p.pin);
        else
            for (const auto &p : bram::kRamb18) wire_up(p.name, p.width, p.out, nullptr, p.name);
        if (first) continue;   // the routing touches none of it
        std::vector<std::string> cps = content_params(b);
        std::string pstr;
        for (size_t i = 0; i < cps.size(); i++) pstr += (i ? ", " : "") + cps[i];
        body << "  " << (b.is36 ? "RAMB36E1" : "RAMB18E1")
             << (pstr.empty() ? "" : " #(" + pstr + ")") << " \\" << iname << " (" << o.str()
             << ");\n";
        if (!cps.empty()) bram_rows += cps.size();
        brams++;
    }
    if (brams)
        std::cerr << "  block RAMs: " << brams << " cut at their boundary, " << bram_rows
                  << " content rows carried\n";

    // ---- DSP48E1: cut, not modelled -------------------------------------
    // Same treatment as a block RAM and for the same reason: nothing here
    // models a multiply-accumulate.  The outputs are cut into free variables
    // and every input becomes an obligation, so what is proved is the
    // BOUNDARY -- which net reaches which pin -- and the two sides' cuts
    // cancel because they name the same primitive over the same pins.
    //
    // Without this the block is simply absent from the extraction, and every
    // cone reading its result differs against a synthesis that has one.  That
    // reads as a place-and-route fault and is not one.
    //
    // Taken from dc.other_tiles, not site_feats: a DSP's configuration is
    // spelled "<tile>.DSP48.DSP_0.<feature>", whose first component names a
    // feature group rather than a site, so the site-feature parser files it
    // under nothing and counts it as skipped.  The clock manager below is
    // reached the same way for the same reason.
    int dsps = 0;
    for (const auto &kv : dc.other_tiles) {
        const std::string &tile = kv.first;
        auto ti = tiles.find(tile);
        if (ti == tiles.end() || ti->second.type.rfind("DSP_", 0) != 0) continue;
        for (const auto &per_site : site_pins[ti->second.type]) {
            if (per_site.empty()) continue;
            // Which of the tile's two sites this is, read off the wires
            // rather than assumed from the map's order.
            std::string site;
            for (const auto &pw : per_site) {
                auto us = pw.second.find('_', 4);
                if (pw.second.rfind("DSP_", 0) == 0 && us != std::string::npos) {
                    site = pw.second.substr(0, us);
                    break;
                }
            }
            if (site.empty()) continue;
            // Only a site the FASM configures.  Every site's pins are in the
            // database whether the design uses them or not, so emitting on
            // the strength of the pin map alone puts a fully wired DSP in the
            // netlist for the tile's OTHER half -- a block the design does
            // not have, reading nets nothing drives.  The features name the
            // site they belong to, so ask them.
            bool configured = false;
            for (const auto &feat : kv.second)
                if (feat.rfind("DSP48." + site + ".", 0) == 0) { configured = true; break; }
            if (!configured) continue;
            std::string iname = sanitise(tile + "_" + site);
            std::ostringstream o;
            bool first = true;
            for (const auto &port : dsp::kDsp48e1) {
                int n = port.width ? port.width : 1;
                std::vector<std::string> bits;   // MSB first, as written
                bool any = false;
                for (int i = n - 1; i >= 0; i--) {
                    std::string pin = port.name;
                    if (port.width) pin += std::to_string(i);
                    std::string bit;
                    auto it = per_site.find(pin);
                    if (it != per_site.end()) {
                        std::string rawnet = tw(tile, it->second);
                        if (port.out) driven_raw.insert(rawnet);
                        bit = emit_net(rawnet);
                    }
                    if (!bit.empty()) any = true;
                    bits.push_back(bit.empty() ? "1'b0" : bit);
                }
                if (!any) continue;
                o << (first ? "" : ", ") << "." << port.name << "(";
                first = false;
                if (port.width) {
                    o << "{";
                    for (size_t i = 0; i < bits.size(); i++) o << (i ? ", " : "") << bits[i];
                    o << "}";
                } else {
                    o << bits[0];
                }
                o << ")";
            }
            if (first) continue;   // the routing touches none of it
            body << "  DSP48E1 \\" << iname << " (" << o.str() << ");\n";
            dsps++;
        }
    }
    if (dsps) std::cerr << "  DSPs cut at their boundary: " << dsps << "\n";

    // ---- DDR registers, cut at their boundary --------------------------
    // Same contract as the block RAMs above: the primitive is instantiated
    // empty, and what the proof asserts is the boundary.  An IDDR's Q1 and Q2
    // become free variables and its D, C, CE and R become obligations; the
    // synthesis side carries the same primitive with the same port names, so
    // the cuts cancel and the cones on either side stay comparable.
    //
    // What this does NOT check is the capture edge, the initial value or the
    // set/reset value.  Two IDDRs with the same boundary and different
    // DDR_CLK_EDGE pass here.  That is a real gap, and the honest one: the
    // alternative is a negedge register in a proof that has no notion of one.
    for (const auto &d : ddr_sites) {
        std::ostringstream o;
        bool first = true;
        for (const auto &pr : d.ports) {
            std::string raw = tw(d.tile, pr.second);
            // Outputs are driven by this instance and by nothing else, the same
            // bookkeeping a block RAM's data outputs get.  A DDR register
            // drives Q/Q1/Q2; a SERDES drives OQ/TQ (OSERDESE2) or O/Q1..Q8
            // (ISERDESE2).  None of these primitives has an INPUT so named.
            if (pr.first == "Q" || pr.first.rfind("Q", 0) == 0 ||
                pr.first == "OQ" || pr.first == "TQ" || pr.first == "O")
                driven_raw.insert(raw);
            o << (first ? "" : ", ") << "." << pr.first << "(" << emit_net(raw) << ")";
            first = false;
        }
        if (first) continue;   // the routing touches none of it
        body << "  " << d.prim << " \\" << d.iname << " (" << o.str() << ");\n";
    }
    if (!ddr_sites.empty())
        std::cerr << "  DDR registers cut at their boundary: " << ddr_sites.size() << "\n";

    // ---- the clock manager's LOCKED pin --------------------------------
    // The MMCM itself is not modelled and cannot usefully be: what comes out
    // of it is a frequency, and this program only reasons about Boolean
    // values.  But one of its pins IS Boolean -- LOCKED, which the reset
    // circuit of practically every LiteX SoC reads -- and leaving it on the
    // interconnect pull-up makes it a CONSTANT, so a reset synchroniser that
    // waits for the PLL compares against 1 and differs for a reason that has
    // nothing to do with the design.  Emitting the block with just that pin
    // makes it a cut point instead: a free variable the placement can pair
    // with the synthesis's own, which is what it honestly is.
    for (const auto &kv : dc.other_tiles) {
        auto ti = tiles.find(kv.first);
        if (ti == tiles.end() || ti->second.type.rfind("CMT_TOP", 0) != 0) continue;
        for (const auto &pins : site_pins[ti->second.type]) {
            auto lk = pins.find("LOCKED");
            if (lk == pins.end()) continue;
            std::string raw = tw(kv.first, lk->second);
            driven_raw.insert(raw);
            body << "  MMCME2_ADV \\" << sanitise(kv.first + "_MMCME2_ADV") << " (.LOCKED("
                 << emit_net(raw) << "));\n";
            break;
        }
    }

    // now the module, in order: ports, internal nets, routing, instances.
    // Taken here, not earlier: resolving a slice's pins adds endpoints.
    std::set<std::string> roots;
    for (const auto &kv : dsu.parent) roots.insert(dsu.find(kv.first));
    std::set<std::string> driven;
    for (const auto &x : driven_raw) driven.insert(sanitise(dsu.find(x)));
    // The interconnect's constant rails are named, not undriven.  A net that
    // reaches GND_WIRE reads 0 and one that reaches VCC_WIRE reads 1; only a
    // net that reaches nothing at all takes the pull-up.  Getting this wrong
    // is invisible in a design without carries -- an unused LUT input reads
    // the same either way -- and fatal in one with them, because a carry
    // chain starting from a grounded CYINIT then starts from 1.
    std::map<std::string, int> rail;   // sanitised root -> the value it is held at
    for (const auto &kv : dsu.parent) {
        const std::string &ep = kv.first;
        auto ends_with = [&](const char *suffix) {
            size_t n = strlen(suffix);
            return ep.size() >= n && ep.compare(ep.size() - n, n, suffix) == 0;
        };
        int v = ends_with("GND_WIRE") ? 0 : ends_with("VCC_WIRE") ? 1 : -1;
        if (v < 0)
            continue;
        std::string root = sanitise(dsu.find(ep));
        auto it = rail.find(root);
        if (it != rail.end() && it->second != v)
            std::cerr << "  warning: " << root << " reaches both rails\n";
        rail[root] = v;
    }

    // Which roots reach a pad, computed ONCE.
    //
    // The two loops below used to ask this per (root, endpoint) pair, which
    // is |roots| x |io_endpoints| calls to dsu.find -- and find walks a
    // std::map keyed by strings, compressing the path as it goes, so every
    // call is many string comparisons rather than an array step.  On the
    // examples that is invisible.  On a Vivado bitstream's fabric, where
    // roots runs to tens of thousands, it is the difference between seconds
    // and not finishing: the extractor sat at 100% CPU here with the hard
    // blocks already cut and fabric.v still empty.
    std::set<std::string> io_roots;
    for (const auto &e : io_endpoints) io_roots.insert(dsu.find(e));

    std::vector<std::string> ports, outs, tied;
    for (const auto &r : roots) {
        std::string n = sanitise(r);
        bool clock = (!clock_root.empty() && r == clock_root);
        if (driven.count(n) && !clock) {
            // driven inside the fabric: only interesting if it reaches a pad
            if (io_roots.count(r)) outs.push_back(n);
            continue;
        }
        bool is_port = (!clock_root.empty() && r == clock_root);
        if (!is_port) is_port = io_roots.count(r) != 0;
        for (const auto &pat : input_pats)
            if (r.find(pat) != std::string::npos) { is_port = true; break; }
        (is_port ? ports : tied).push_back(n);
    }
    int railed = 0;
    for (const auto &t : tied)
        railed += rail.count(t) != 0;

    // a port keeps the design's own name where the XDC gave one
    std::map<std::string, std::string> root_of;   // sanitised name -> its net root
    for (const auto &r : roots) root_of[sanitise(r)] = r;

    // A bidirectional pad reaches the fabric as two separate nets -- one the
    // design drives, one it reads -- and the constraints give both the same
    // name.  Sharing a name fuses them, and the extraction then claims the
    // design reads back exactly what it drives, which is only true while the
    // pad is not tri-stated.  The synthesis makes no such claim: its IOBUFDS
    // presents whatever is on the pad.  So the receiving side keeps the name
    // and the driving side keeps its own, which leaves the two sides of the
    // comparison making the same assumption.
    {
        std::map<std::string, std::string> port_named;
        for (const auto &n : ports) {
            auto f = friendly.find(root_of[n]);
            if (f != friendly.end()) port_named[f->second] = n;
        }
        int split = 0, kept_on_drive = 0;
        for (const auto &n : outs) {
            auto f = friendly.find(root_of[n]);
            if (f == friendly.end() || !port_named.count(f->second)) continue;
            // A pad is bidirectional only if the design also reads the receive
            // side.  The IOB-site seed puts that side in the graph for every
            // pad; if nothing in the fabric consumes it, the pad is output-only
            // and the name stays on what the design drives.
            const std::string &recv = port_named[f->second];
            const bool fabric_reads_receive = read_roots.count(root_of[recv]) != 0;
            if (!fabric_reads_receive) {
                friendly.erase(root_of[recv]);
                kept_on_drive++;
                continue;
            }
            friendly.erase(f);
            split++;
        }
        if (split)
            std::cerr << "  " << split << " bidirectional pad(s): the name follows what the design"
                      << " reads, since what it drives is not what it must read back\n";
        if (kept_on_drive)
            std::cerr << "  " << kept_on_drive << " output-only pad(s): the receive side is unused, so"
                      << " the name stays on what the design drives\n";
    }

    std::vector<std::string> port_decl, out_decl;
    std::map<std::string, std::string> emit_as;
    for (const auto &r : roots) {
        std::string n = sanitise(r);
        auto f = friendly.find(r);
        if (f != friendly.end()) emit_as[n] = "\\" + f->second + " ";
    }
    for (const auto &n : ports) port_decl.push_back(emit_as.count(n) ? emit_as[n] : n);
    for (const auto &n : outs) out_decl.push_back(emit_as.count(n) ? emit_as[n] : n);
    // A bidirectional pad is reached from two sides -- something in the fabric
    // drives it and something else reads it back -- and the constraints give
    // both the same name.  Declared twice it is not Verilog at all, so it is
    // declared once, as the inout it is, and named so the reader knows the
    // two directions are not the same net here.
    std::vector<std::string> inout_decl;
    {
        std::set<std::string> as_out(out_decl.begin(), out_decl.end());
        std::vector<std::string> kept;
        for (const auto &n : port_decl) {
            if (as_out.count(n)) inout_decl.push_back(n);
            else kept.push_back(n);
        }
        port_decl.swap(kept);
        if (!inout_decl.empty()) {
            std::vector<std::string> keep_out;
            std::set<std::string> bidir(inout_decl.begin(), inout_decl.end());
            for (const auto &n : out_decl)
                if (!bidir.count(n)) keep_out.push_back(n);
            out_decl.swap(keep_out);
            std::cerr << "  " << inout_decl.size() << " bidirectional pad(s): what the design"
                      << " reads back is whatever is on the pad, not what it drives\n";
        }
    }
    os << "// " << dsu.parent.size() << " (tile,wire) endpoints -> " << roots.size()
       << " nets, joined by " << joins << " tileconn pairs\n"
       << "// " << ports.size() << " inputs, " << outs.size() << " outputs, "
       << (tied.size() - size_t(railed)) << " undriven nets at the interconnect pull-up, "
       << railed << " held at a GND/VCC rail\n"
       << "module fabric (\n";
    for (size_t i = 0; i < port_decl.size(); i++)
        os << "  input wire " << port_decl[i]
           << (i + 1 < port_decl.size() || !out_decl.empty() || !inout_decl.empty() ? ",\n" : "\n");
    for (size_t i = 0; i < out_decl.size(); i++)
        os << "  output wire " << out_decl[i]
           << (i + 1 < out_decl.size() || !inout_decl.empty() ? ",\n" : "\n");
    for (size_t i = 0; i < inout_decl.size(); i++)
        os << "  inout wire " << inout_decl[i] << (i + 1 < inout_decl.size() ? ",\n" : "\n");
    os << ");\n";
    std::set<std::string> is_port(ports.begin(), ports.end());
    is_port.insert(outs.begin(), outs.end());
    for (const auto &r : roots) {
        std::string n = sanitise(r);
        if (driven.count(n) && !is_port.count(n)) os << "  wire " << emit_net(r) << ";\n";
    }
    for (const auto &t : tied) {
        auto rv = rail.find(t);
        bool on_rail = rv != rail.end();
        os << "  wire " << (emit_as.count(t) ? emit_as[t] : t) << " = 1'b"
           << (on_rail ? rv->second : pullup) << ";   // "
           << (on_rail ? (rv->second ? "VCC rail" : "GND rail") : "undriven") << "\n";
    }
    os << "\n";
    if (timing) {
        // Transport delay per routing assign, as nextpnr computes it from the
        // same database: the PIP's own delay, plus RC -- its output resistance
        // times everything hanging off its destination, and the resistance
        // driving its source times the capacitance its source is loaded with,
        // which is the sum of the input capacitances of every PIP used from
        // that source.  fast_min and slow_max are kept; the corner is chosen
        // at simulation time (iverilog -Tmin / -Tmax) or by the STA.
        auto split = [](const std::string &tw_) {
            auto sl = tw_.find('/');
            return std::make_pair(tw_.substr(0, sl), sl == std::string::npos ? std::string() : tw_.substr(sl + 1));
        };
        auto lookup = [&](const std::string &dst, const std::string &src) -> const PipT * {
            auto d = split(dst), sr = split(src);
            auto ti = tiles.find(d.first);
            if (ti == tiles.end()) return nullptr;
            auto pt = pip_timing.find(ti->second.type);
            if (pt == pip_timing.end()) return nullptr;
            auto it = pt->second.find(sr.second + "\n" + d.second);
            return it == pt->second.end() ? nullptr : &it->second;
        };
        std::map<std::string, double> load_cap, drive_res;
        for (const auto &a : assigns) {
            const PipT *t = lookup(a.first, a.second);
            if (!t) continue;
            load_cap[a.second] += t->in_cap;
            drive_res[a.first] = t->res;
        }
        int timed = 0;
        for (const auto &a : assigns) {
            const PipT *t = lookup(a.first, a.second);
            std::string delay;
            if (t) {
                auto d = split(a.first);
                auto ti = tiles.find(d.first);
                std::pair<double, double> rc{0, 0};
                auto wr = wire_rc.find(ti->second.type);
                if (wr != wire_rc.end()) { auto w = wr->second.find(d.second); if (w != wr->second.end()) rc = w->second; }
                double src_r = drive_res.count(a.second) ? drive_res[a.second] : 0.0;
                // mOhm * pF = ps, and the delays are in ns
                double extra = (src_r * load_cap[a.second] + (t->res + rc.second / 2) * rc.first) / 1e9;
                char buf[96];
                snprintf(buf, sizeof buf, "#(%.3f:%.3f:%.3f) ", t->fmin + extra, t->smax + extra, t->smax + extra);
                delay = buf; timed++;
            } else {
                delay = "#(0.020:0.020:0.020) ";   // a PIP the database has no figure for: a stub
            }
            os << "  assign " << delay << emit_net(a.first) << " = " << emit_net(a.second) << ";\n";
        }
        std::cerr << "  timing: " << timed << " of " << assigns.size() << " routing assigns carry a database delay\n";
        if (!net_delays_path.empty()) {
            // Every net's delay from its driver to each load, by SITE PIN
            // (SLICE_X10Y20/AQ), which is how Vivado's get_net_delays names
            // the same thing: the two CSVs join on those two columns, and
            // the difference is the model's error on that route.
            // A wire that continues into the next tile is the same node under
            // another name (tileconn), and the union-find already knows it:
            // the walk goes by union root, and a root's members are searched
            // for the one that is a site pin.
            std::map<std::string, std::vector<std::pair<std::string, std::pair<double, double>>>> down; // root -> (root, d)
            std::set<std::string> has_src;
            std::map<std::string, std::vector<std::string>> members;
            for (const auto &a : assigns) {
                members[dsu.find(a.first)].push_back(a.first);
                members[dsu.find(a.second)].push_back(a.second);
            }
            for (const auto &a : assigns) {
                const PipT *t = lookup(a.first, a.second);
                std::pair<double, double> d{0.02, 0.02};
                if (t) {
                    auto dd = split(a.first);
                    auto ti = tiles.find(dd.first);
                    std::pair<double, double> rc{0, 0};
                    auto wr = wire_rc.find(ti->second.type);
                    if (wr != wire_rc.end()) { auto w = wr->second.find(dd.second); if (w != wr->second.end()) rc = w->second; }
                    double src_r = drive_res.count(a.second) ? drive_res[a.second] : 0.0;
                    double extra = (src_r * load_cap[a.second] + (t->res + rc.second / 2) * rc.first) / 1e9;
                    d = {t->fmin + extra, t->smax + extra};
                }
                down[dsu.find(a.second)].push_back({dsu.find(a.first), d});
                has_src.insert(dsu.find(a.first));
            }
            // a wire's site pin, if it is one: "<site>/<pin>"
            auto site_pin_of_wire = [&](const std::string &tw_) -> std::string {
                auto d = split(tw_);
                auto ti = tiles.find(d.first);
                if (ti == tiles.end()) return "";
                auto sp = site_pins.find(ti->second.type);
                if (sp == site_pins.end()) return "";
                for (size_t i = 0; i < sp->second.size() && i < ti->second.sites.size(); i++)
                    for (const auto &pw : sp->second[i])
                        if (pw.second == d.second) return ti->second.sites[i].first + "/" + pw.first;
                return "";
            };
            auto site_pin = [&](const std::string &root) -> std::string {
                auto m = members.find(root);
                if (m == members.end()) return site_pin_of_wire(root);
                for (const auto &w : m->second) { std::string sp = site_pin_of_wire(w); if (!sp.empty()) return sp; }
                return "";
            };
            std::ofstream nd(net_delays_path);
            nd << "from,to,fast_min,slow_max\n";
            long rows = 0;
            for (const auto &kv : down) {
                if (has_src.count(kv.first)) continue;          // not a root
                std::string from = site_pin(kv.first);
                if (from.empty()) from = sanitise(kv.first);
                // DFS from the root, accumulating
                std::vector<std::pair<std::string, std::pair<double, double>>> st{{kv.first, {0, 0}}};
                std::set<std::string> seen;
                while (!st.empty()) {
                    auto cur = st.back(); st.pop_back();
                    if (!seen.insert(cur.first).second) continue;
                    auto it = down.find(cur.first);
                    if (it == down.end()) {
                        std::string to = site_pin(cur.first);
                        if (!to.empty()) { nd << from << "," << to << "," << cur.second.first << "," << cur.second.second << "\n"; rows++; }
                        continue;
                    }
                    for (const auto &nx : it->second)
                        st.push_back({nx.first, {cur.second.first + nx.second.first, cur.second.second + nx.second.second}});
                }
            }
            std::cerr << "  net delays: " << rows << " driver->load pairs written to " << net_delays_path << "\n";
        }
    } else {
        for (const auto &a : assigns)
            os << "  assign " << emit_net(a.first) << " = " << emit_net(a.second) << ";\n";
    }
    for (const auto &w : carry_wires) os << "  wire " << w << ";\n";
    for (const auto &w : helper_wires) os << "  wire " << w << ";\n";
    for (const auto &a : carry_assigns) os << "  assign " << a.first << " = " << a.second << ";\n";
    os << "\n" << body.str() << "endmodule\n";

    if (simple_clock && one_clock)
        std::cerr << "  clock tree simplified: " << clocked << " slice clocks joined to "
                  << bufg_outs.size() << " BUFG output\n";
    else if (simple_clock && bufg_outs.size() > 1)
        std::cerr << "  " << bufg_outs.size() << " BUFG outputs: clock tree left to the routing,"
                  << " since one clock per design is what the simplification assumes\n";
    std::cerr << "tileverilog: " << dc.slices.size() << " slices, " << inst << " column instances, "
              << assigns.size() << " routing assigns, " << roots.size() << " nets"
              << " (net growth settled in " << rounds << " rounds)\n";
    if (unmodelled) std::cerr << "  " << unmodelled << " slice features not modelled (see tiledump --gaps)\n";
    if (skipped_site_cfg) std::cerr << "  " << skipped_site_cfg << " non-slice site features skipped\n";
    return 0;
}
