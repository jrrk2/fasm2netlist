#include "lvs/regmap.hpp"

#include "json.hpp"

#include "bram_ports.hpp"
#include "dsp_ports.hpp"
#include "gtpins.hpp"

#include <algorithm>
#include <cctype>
#include <regex>
#include <cstdlib>
#include <fstream>
#include <sstream>
#include <stdexcept>
#include <set>
#include <vector>

namespace lvs {

namespace {

std::string slurp(const std::string &p)
{
    std::ifstream f(p);
    if (!f)
        throw std::runtime_error("cannot open " + p);
    std::ostringstream ss;
    ss << f.rdbuf();
    return ss.str();
}

// A block RAM's data outputs, which are the pins a comparison cuts at.  The
// widths come from the same table the extractor and the tile model use, so a
// port that is 32 bits wide is 32 bits wide in all three.  Everything else a
// block RAM drives -- ECC, cascade, FIFO status -- is not data and is not cut.
std::vector<std::pair<std::string, int>> data_outs(bool is36)
{
    std::vector<std::pair<std::string, int>> v;
    if (is36) {
        for (const auto &p : bram::kRamb36)
            if (p.out && std::string(p.port).rfind("DO", 0) == 0) v.push_back({p.port, p.width});
    } else {
        for (const auto &p : bram::kRamb18)
            if (p.out && std::string(p.name).rfind("DO", 0) == 0) v.push_back({p.name, p.width});
    }
    return v;
}

}  // namespace

RegMap build_regmap(const std::string &placement_path, const std::string &gold_json_path,
                    const std::string &db, const std::string &device)
{
    RegMap out;
    json::Value place = json::parse(slurp(placement_path));
    json::Value goldj = json::parse(slurp(gold_json_path));
    json::Value grid = json::parse(slurp(db + "/" + device + "/tilegrid.json"));

    // The gold module: the one flagged top, else the sole non-blackbox.
    const json::Value *mod = nullptr;
    for (const auto &kv : goldj.get("modules").members())
        if (!kv.second.get("attributes").get("top").isNull()) {
            mod = &kv.second;
            out.module = kv.first;
        }
    if (!mod)
        for (const auto &kv : goldj.get("modules").members())
            if (kv.second.get("attributes").get("blackbox").isNull()) {
                mod = &kv.second;
                out.module = kv.first;
            }
    if (!mod)
        throw std::runtime_error("no top module in " + gold_json_path);

    // Net id -> the source signal's name for it.  Hidden names are yosys's own
    // invention ($abc$...) and tell the reader nothing, so they are skipped;
    // the first real name to claim a bit wins.
    std::map<int64_t, std::string> label;
    std::map<int64_t, std::vector<std::string>> alt_label;
    for (const auto &nn : mod->get("netnames").members()) {
        const json::Value &hide = nn.second.get("hide_name");
        bool hidden = !hide.isNull() && hide.asInt() != 0;
        const auto &bits = nn.second.get("bits").items();
        // A vector need not start at zero.  `wire [4:2] o_cnt` is bits 0..2 of
        // the JSON's list and o_cnt[2]..o_cnt[4] of every name anyone writes,
        // and yosys records the difference as "offset" -- which, ignored, does
        // not lose a name so much as invent a wrong one: o_cnt[0] labels the
        // register the design calls o_cnt[2].  `upto` says the declaration ran
        // the other way, [2:4], so the list is most significant first.
        // Only three netnames in the LiteX SoC carry a non-zero offset, and
        // one of them is the CPU's state counter, which most of the design
        // reads; a single mislabelled register is not one bad cone but every
        // cone downstream of it.
        int64_t offset = 0;
        {
            const json::Value &o = nn.second.get("offset");
            if (!o.isNull()) offset = o.asInt();
        }
        const json::Value &up = nn.second.get("upto");
        bool upto = !up.isNull() && up.asInt() != 0;
        for (size_t i = 0; i < bits.size(); i++) {
            if (bits[i].type != json::Type::Int)
                continue;
            int64_t b = bits[i].asInt();
            int64_t idx = offset + (upto ? int64_t(bits.size()) - 1 - int64_t(i) : int64_t(i));
            std::string nm = bits.size() == 1 && offset == 0
                                 ? nn.first
                                 : nn.first + "[" + std::to_string(idx) + "]";
            // Every name, hidden or not, is a CANDIDATE: the caller has to
            // find whichever one its own netlist emitted, and write_verilog
            // does not always choose the same one as this does.  Only the
            // preferred label skips hidden names, and only because a report
            // reads better with "wdata0_r[0]" in it than "_0565_".
            alt_label[b].push_back(nm);
            // A one-bit VECTOR is written both ways: the JSON netname is bare
            // ("wdata0_r"), and write_verilog emits it indexed
            // ("wdata0_r[0]") because it was declared [0:0].  Neither spelling
            // is more correct, and the caller cannot know which its netlist
            // used, so offer both.
            if (bits.size() == 1)
                alt_label[b].push_back(nn.first + "[" + std::to_string(idx) + "]");
            if (bits.size() == 1 && offset == 0)
                alt_label[b].push_back(nn.first);
            if (!hidden && !label.count(b))
                label[b] = nm;
        }
    }
    // A bit no real name claimed still needs one, or its register goes
    // unmatched -- and an unmatched register is not one missing cone, it makes
    // every cone downstream of it incomparable too.
    for (const auto &[b, names] : alt_label)
        if (!label.count(b) && !names.empty())
            label[b] = names.front();

    // site pins, per tile type, in the order the tile lists its sites
    std::map<std::string, std::vector<std::map<std::string, std::string>>> tt_pins;
    auto pins_for = [&](const std::string &tile, const std::string &site) {
        std::map<std::string, std::string> none;
        const json::Value &tv = grid.get(tile);
        if (tv.isNull())
            return none;
        std::string type = tv.get("type").asString();
        if (!tt_pins.count(type)) {
            std::vector<std::map<std::string, std::string>> per;
            try {
                json::Value tt = json::parse(slurp(db + "/tile_type_" + type + ".json"));
                for (const auto &sv : tt.get("sites").items()) {
                    std::map<std::string, std::string> m;
                    for (const auto &pk : sv.get("site_pins").members())
                        m[pk.first] = pk.second.get("wire").asString();
                    per.push_back(m);
                }
            } catch (const std::exception &) {
                // a tile type we have no model for contributes no labels
            }
            tt_pins[type] = per;
        }
        // The placement names a site absolutely (SLICE_X0Y100); the tile type
        // describes its sites positionally.  Ranking the tile's slices by X
        // recovers the ordinal the tile type is indexed by.
        std::vector<std::pair<int, std::string>> slices;
        for (const auto &sv : tv.get("sites").members()) {
            if (sv.first.rfind("SLICE_X", 0) != 0)
                continue;
            slices.push_back({atoi(sv.first.c_str() + 7), sv.first});
        }
        std::sort(slices.begin(), slices.end());
        for (size_t i = 0; i < slices.size(); i++)
            if (slices[i].second == site && i < tt_pins[type].size())
                return tt_pins[type][i];
        return none;
    };

    // Memories.  A placement cell called "<ram>/DPR<n>" at a site's <col>6LUT
    // is port n of that synthesis RAM held in that fabric column.  The
    // netlists name the site differently -- the placement absolutely
    // (SLICE_X42Y136), the fabric by the local suffix FASM uses (SLICEM_X0) --
    // so the ordinal has to be recovered here, where the tile grid is already
    // open.
    auto sanitise = [](const std::string &in) {
        std::string r;
        for (char c : in) r.push_back(isalnum((unsigned char)c) ? c : '_');
        return r;
    };
    {
        static const std::regex dpr(R"(^(.*)/DPR(\d)(?:_(\d))?$)");
        for (const auto &pv : place.members()) {
            if (pv.second.get("type").asString() != "SLICE_LUTX") continue;
            std::smatch m;
            const std::string cell = pv.first;
            if (!std::regex_match(cell, m, dpr)) continue;
            std::string bel = pv.second.get("bel").asString();
            if (bel.empty() || bel[0] < 'A' || bel[0] > 'D') continue;
            std::string tile = pv.second.get("tile").asString();
            std::string site = pv.second.get("site").asString();
            const json::Value &tv = grid.get(tile);
            if (tv.isNull()) continue;
            std::vector<std::pair<int, std::string>> sl;
            for (const auto &sv : tv.get("sites").members())
                if (sv.first.rfind("SLICE_X", 0) == 0)
                    sl.push_back({atoi(sv.first.c_str() + 7), sv.first});
            std::sort(sl.begin(), sl.end());
            int ord = -1;
            for (size_t i = 0; i < sl.size(); i++)
                if (sl[i].second == site) ord = int(i);
            if (ord < 0) continue;
            std::string stype = tv.get("sites").get(site).asString();
            std::string gate = sanitise(tile + "_" + stype + "_X" + std::to_string(ord) + "_" +
                                        std::string(1, bel[0]));
            char port = char('A' + (m[2].str()[0] - '0'));
            int nbits = m[3].matched ? 2 : 1;
            for (int d = 0; d < nbits; d++)
                out.mem[gate + ":DO[" + std::to_string(d) + "]"] =
                    m[1].str() + ":DO" + port + "[" + std::to_string(d) + "]";
        }
    }

    // Shift registers.  An SRL16E sits at a column's 6LUT (the upper half of a 32-bit LUT, read as O6) or its 5LUT (the lower, O5); an
    // SRLC32E at the 6LUT and takes the whole LUT.  The tile model names the cut after the column's site, as for a RAM.
    {
        const json::Value &gcells = mod->get("cells");
        for (const auto &pv : place.members()) {
            if (pv.second.get("type").asString() != "SLICE_LUTX") continue;
            const json::Value &gc = gcells.get(pv.first);
            if (gc.isNull()) continue;
            std::string gtype = gc.get("type").asString();
            if (gtype != "SRL16E" && gtype != "SRLC16E" && gtype != "SRLC32E") continue;
            std::string bel = pv.second.get("bel").asString();
            if (bel.size() < 2 || bel[0] < 'A' || bel[0] > 'D') continue;
            std::string tile = pv.second.get("tile").asString();
            std::string site = pv.second.get("site").asString();
            const json::Value &tv = grid.get(tile);
            if (tv.isNull()) continue;
            std::vector<std::pair<int, std::string>> sl;
            for (const auto &sv : tv.get("sites").members())
                if (sv.first.rfind("SLICE_X", 0) == 0)
                    sl.push_back({atoi(sv.first.c_str() + 7), sv.first});
            std::sort(sl.begin(), sl.end());
            int ord = -1;
            for (size_t i = 0; i < sl.size(); i++)
                if (sl[i].second == site) ord = int(i);
            if (ord < 0) continue;
            std::string stype = tv.get("sites").get(site).asString();
            std::string gate = sanitise(tile + "_" + stype + "_X" + std::to_string(ord) + "_" + std::string(1, bel[0]));
            int d = gtype == "SRLC32E" ? 0 : (bel[1] == '6' ? 1 : 0);
            out.mem[gate + ":SRL[" + std::to_string(d) + "]"] = pv.first + ":Q[0]";
        }
    }

    // The deeper single-port RAMs.  A placement cell "<ram>/ADDR<n>" is one
    // column of a RAM128X1S or RAM256X1S (nextpnr's packer names them so,
    // and the Vivado placement dump follows it), and the tile model reads
    // the whole group out on one mux, under a name built from the site plus
    // the group: _M256 for the slice, _M128AB or _M128CD for a pair.  Any
    // one column of the group locates it.
    // A RAM64X1D / RAM32X1D packs into two columns, <ram>/SP and <ram>/DP
    // (nextpnr's names), each reading one port: SPO at the write address, DPO
    // at DPRA.  Each column's read is its port's.
    {
        static const std::regex dual(R"(^(.*)/(SP|DP)$)");
        const json::Value &gcells = mod->get("cells");
        for (const auto &pv : place.members()) {
            if (pv.second.get("type").asString() != "SLICE_LUTX") continue;
            std::smatch m;
            const std::string cell = pv.first;
            if (!std::regex_match(cell, m, dual)) continue;
            const json::Value &gc = gcells.get(m[1].str());
            if (gc.isNull()) continue;
            std::string gtype = gc.get("type").asString();
            if (gtype != "RAM64X1D" && gtype != "RAM32X1D") continue;
            std::string bel = pv.second.get("bel").asString();
            if (bel.empty() || bel[0] < 'A' || bel[0] > 'D') continue;
            std::string tile = pv.second.get("tile").asString();
            std::string site = pv.second.get("site").asString();
            const json::Value &tv = grid.get(tile);
            if (tv.isNull()) continue;
            std::vector<std::pair<int, std::string>> sl;
            for (const auto &sv : tv.get("sites").members())
                if (sv.first.rfind("SLICE_X", 0) == 0)
                    sl.push_back({atoi(sv.first.c_str() + 7), sv.first});
            std::sort(sl.begin(), sl.end());
            int ord = -1;
            for (size_t i = 0; i < sl.size(); i++)
                if (sl[i].second == site) ord = int(i);
            if (ord < 0) continue;
            std::string stype = tv.get("sites").get(site).asString();
            std::string gate = sanitise(tile + "_" + stype + "_X" + std::to_string(ord) + "_" + std::string(1, bel[0]));
            out.mem[gate + ":DO[0]"] = m[1].str() + ":" + m[2].str() + "O[0]";
        }
    }

    {
        static const std::regex addr(R"(^(.*)/ADDR(\d)$)");
        const json::Value &gcells = mod->get("cells");
        for (const auto &pv : place.members()) {
            if (pv.second.get("type").asString() != "SLICE_LUTX") continue;
            std::smatch m;
            const std::string cell = pv.first;
            if (!std::regex_match(cell, m, addr)) continue;
            const json::Value &gc = gcells.get(m[1].str());
            if (gc.isNull()) continue;
            std::string gtype = gc.get("type").asString();
            if (gtype != "RAM256X1S" && gtype != "RAM128X1S") continue;
            std::string bel = pv.second.get("bel").asString();
            if (bel.empty() || bel[0] < 'A' || bel[0] > 'D') continue;
            std::string tile = pv.second.get("tile").asString();
            std::string site = pv.second.get("site").asString();
            const json::Value &tv = grid.get(tile);
            if (tv.isNull()) continue;
            std::vector<std::pair<int, std::string>> sl;
            for (const auto &sv : tv.get("sites").members())
                if (sv.first.rfind("SLICE_X", 0) == 0)
                    sl.push_back({atoi(sv.first.c_str() + 7), sv.first});
            std::sort(sl.begin(), sl.end());
            int ord = -1;
            for (size_t i = 0; i < sl.size(); i++)
                if (sl[i].second == site) ord = int(i);
            if (ord < 0) continue;
            std::string stype = tv.get("sites").get(site).asString();
            std::string suffix = gtype == "RAM256X1S" ? "_M256"
                               : (bel[0] == 'C' || bel[0] == 'D') ? "_M128CD" : "_M128AB";
            std::string gate = sanitise(tile + "_" + stype + "_X" + std::to_string(ord)) + suffix;
            out.mem[gate + ":O[0]"] = m[1].str() + ":O[0]";
        }
    }

    // Block RAM.  Nothing here has to understand what the memory does: the
    // placement says which synthesis cell sits in which site, the tile model
    // names its instance after that site, and pairing the two is enough for
    // the checker to cut both at the same place and then prove the boundary.
    // A RAMB18 site is the tile's lower or upper 18Kb half, which FASM -- and
    // so the tile model -- calls RAMB18_Y0 and RAMB18_Y1; the placement names
    // it absolutely (RAMB18_X2Y58), so the half has to be recovered here,
    // where the tile grid is already open.
    {
        for (const auto &pv : place.members()) {
            std::string bel = pv.second.get("bel").asString();
            bool is36 = bel == "RAMB36E1";
            if (bel != "RAMB18E1" && !is36) continue;
            std::string tile = pv.second.get("tile").asString();
            std::string site = pv.second.get("site").asString();
            const json::Value &tv = grid.get(tile);
            if (tv.isNull()) continue;
            std::string fasm_site = "RAMB36_Y0";
            if (!is36) {
                std::vector<std::pair<int, std::string>> halves;
                for (const auto &sv : tv.get("sites").members()) {
                    if (sv.first.rfind("RAMB18_", 0) != 0) continue;
                    auto y = sv.first.rfind('Y');
                    if (y == std::string::npos) continue;
                    halves.push_back({atoi(sv.first.c_str() + y + 1), sv.first});
                }
                std::sort(halves.begin(), halves.end());
                int ord = -1;
                for (size_t i = 0; i < halves.size(); i++)
                    if (halves[i].second == site) ord = int(i);
                if (ord < 0) continue;
                fasm_site = "RAMB18_Y" + std::to_string(ord);
            }
            std::string gate = sanitise(tile + "_" + fasm_site);
            for (const auto &dp : data_outs(is36))
                for (int b = 0; b < dp.second; b++) {
                    std::string suffix =
                        std::string(":") + dp.first + "[" + std::to_string(b) + "]";
                    out.mem[gate + suffix] = pv.first + suffix;
                }
        }
    }

    // The clock manager.  Only its LOCKED pin is paired, and only because it
    // is the one Boolean thing about an MMCM; see the note in src/lvs/cone.cpp
    // for what that does and does not establish.
    for (const auto &pv : place.members()) {
        std::string bel = pv.second.get("bel").asString();
        if (bel != "MMCME2_ADV" && bel != "PLLE2_ADV") continue;
        std::string gate = sanitise(pv.second.get("tile").asString() + "_MMCME2_ADV");
        out.mem[gate + ":LOCKED[0]"] = pv.first + ":LOCKED[0]";
    }

    // The hard-block census.  Every block the placement put somewhere, with
    // the name the tile model would give it if it models that kind at all.
    // Nothing here compares behaviour -- a hard block has no cones to compare
    // -- but a block the synthesis asked for and the bitstream does not
    // configure is a real fault that register matching cannot see.
    {
        // The pins a DDR cut turns into free variables -- see OPAQUE_OUT
        // in cone.cpp, which must cut exactly these.
        static const std::vector<const char *> kIddrOuts = {"Q1", "Q2"};
        static const std::vector<const char *> kOddrOuts = {"Q"};
        // A wide SERDES is cut the same way, so its outputs need the same
        // correspondence.  OSERDESE2 drives OQ (and TQ on a tristate); an
        // ISERDESE2 presents the captured word on Q1..Q8 and its combinational
        // tap on O.
        static const std::vector<const char *> kOserdesOuts = {"OQ", "TQ"};
        static const std::vector<const char *> kIserdesOuts = {"O",  "Q1", "Q2", "Q3",
                                                               "Q4", "Q5", "Q6", "Q7", "Q8"};
        static const std::set<std::string> kHardBels = {
            "RAMB18E1", "RAMB36E1", "DSP48E1",  "MMCME2_ADV",    "PLLE2_ADV",
            // Enumerated from the synthesis, so the names here are the ones
            // yosys emits: a design needing no dynamic reconfiguration gets
            // the BASE primitive, and the census must know it or the block
            // goes uncounted.
            "MMCME2_BASE", "PLLE2_BASE",
            "BUFGCTRL", "BUFR",     "BUFIO",    "IBUFDS_GTE2",   "GTXE2_CHANNEL",
            "GTXE2_COMMON", "GTPE2_CHANNEL", "GTPE2_COMMON", "IDELAYCTRL",
            // The DDR registers in an I/O site.  The tile model cuts these at
            // their boundary, so they need the same correspondence a block RAM
            // gets: without it the two sides carry the same primitive under
            // different names and the cuts cannot cancel.
            "IDDR", "ODDR",
            // The wide SERDES an I/O site can hold instead of a plain DDR
            // register.  LiteX drives every DDR-memory output through an
            // OSERDESE2 and captures the read data through an ISERDESE2; cut at
            // their boundary they pair like an ODDR, and without them every
            // ddram_* port differs on the strength of an undriven pad.
            "ISERDESE2", "OSERDESE2",
        };
        // Enumerated from the SYNTHESIS, not from the placement.  The
        // placement is written at the end of place-and-route, so a cell that
        // was dropped along the way is simply not in it -- which is precisely
        // the case worth catching, and a census built from the placement
        // cannot see it by construction.
        // Which cell output drives each net bit, to follow a BUFG's input back to its source.
        auto bitkey = [](const json::Value &v) { return v.isString() ? v.asString() : std::to_string(v.asInt()); };
        std::map<std::string, std::pair<std::string, std::string>> driver;      // bit -> (cell, port)
        for (const auto &cv : mod->get("cells").members())
            for (const auto &pd : cv.second.get("port_directions").members())
                if (pd.second.asString() == "output")
                    for (const auto &b : cv.second.get("connections").get(pd.first).items())
                        if (!b.isString() || (b.asString() != "0" && b.asString() != "1" && b.asString() != "x"))
                            driver[bitkey(b)] = {cv.first, pd.first};
        for (const auto &cv : mod->get("cells").members()) {
            std::string bel = cv.second.get("type").asString();
            if (bel.rfind("BUFG", 0) == 0) {
                const json::Value &pb = place.get(cv.first);
                if (!pb.isNull()) {
                    out.bufg_site[cv.first] = pb.get("site").asString();
                    for (const char *ip : {"I", "I0"}) {
                        const auto &bits = cv.second.get("connections").get(ip).items();
                        if (bits.empty()) continue;
                        auto d = driver.find(bitkey(bits[0]));
                        if (d == driver.end()) break;
                        const json::Value *pdp = &place.get(d->second.first);
                        // An IBUF/IBUFDS is merged into the pad by the packer and has no placement of its own: its pad's does.
                        if (pdp->isNull() && cv.second.get("type").asString() != "" ) {
                            const std::string dty = mod->get("cells").get(d->second.first).get("type").asString();
                            if (dty.rfind("IBUF", 0) == 0) {
                                const auto &ib = mod->get("cells").get(d->second.first).get("connections").get("I").items();
                                if (!ib.empty())
                                    for (const auto &nn : mod->get("netnames").members())
                                        for (const auto &nb : nn.second.get("bits").items())
                                            if (bitkey(nb) == bitkey(ib[0]) && !place.get(nn.first).isNull() &&
                                                place.get(nn.first).get("type").asString() == "PAD") {
                                                pdp = &place.get(nn.first);
                                                break;
                                            }
                            }
                        }
                        if (pdp->isNull()) break;
                        const json::Value &pd = *pdp;
                        std::string dbel = pd.get("bel").asString(), port = d->second.second;
                        bool named = dbel.rfind("MMCME2", 0) == 0 || dbel.rfind("PLLE2", 0) == 0 || dbel.rfind("GTXE2", 0) == 0;
                        out.bufg_src[pb.get("site").asString()] = pd.get("tile").asString() + " " + (named ? port : std::string("-"));
                        break;
                    }
                }
            }
            if (!kHardBels.count(bel)) continue;
            RegMap::HardBlock hb;
            hb.type = bel;
            const json::Value &pv2 = place.get(cv.first);
            if (pv2.isNull()) {
                // In the synthesis, nowhere in the placement: it did not
                // survive packing.
                hb.site = "";
                out.hard[cv.first] = hb;
                continue;
            }
            hb.site = pv2.get("site").asString();
            std::string tile = pv2.get("tile").asString();
            // Only the kinds the tile model actually emits get a gate name; the
            // rest are reported as unmodelled, which is the honest answer.
            if (bel == "RAMB18E1" || bel == "RAMB36E1") {
                const json::Value &tv = grid.get(tile);
                std::string fasm_site = bel == "RAMB36E1" ? "RAMB36_Y0" : "";
                if (fasm_site.empty() && !tv.isNull()) {
                    std::vector<std::pair<int, std::string>> halves;
                    for (const auto &sv : tv.get("sites").members()) {
                        if (sv.first.rfind("RAMB18_", 0) != 0) continue;
                        auto y = sv.first.rfind('Y');
                        if (y != std::string::npos)
                            halves.push_back({atoi(sv.first.c_str() + y + 1), sv.first});
                    }
                    std::sort(halves.begin(), halves.end());
                    for (size_t i = 0; i < halves.size(); i++)
                        if (halves[i].second == hb.site) fasm_site = "RAMB18_Y" + std::to_string(i);
                }
                if (!fasm_site.empty()) hb.gate_name = sanitise(tile + "_" + fasm_site);
            } else if (bel == "MMCME2_ADV" || bel == "PLLE2_ADV") {
                hb.gate_name = sanitise(tile + "_MMCME2_ADV");
            } else if (bel == "DSP48E1") {
                // The placement names the site as the device does, DSP48_X2Y56;
                // the FASM and the tile model name it by its position within
                // the tile, DSP_0 or DSP_1.  Index the tile's sites of that
                // kind rather than parsing the Y, exactly as the RAMB18 halves
                // above are.
                const json::Value &tv = grid.get(tile);
                std::string fasm_site;
                if (!tv.isNull()) {
                    std::vector<std::pair<int, std::string>> at;
                    for (const auto &sv : tv.get("sites").members()) {
                        if (sv.first.rfind("DSP48_", 0) != 0) continue;
                        auto y = sv.first.rfind('Y');
                        if (y != std::string::npos)
                            at.push_back({atoi(sv.first.c_str() + y + 1), sv.first});
                    }
                    std::sort(at.begin(), at.end());
                    for (size_t i = 0; i < at.size(); i++)
                        if (at[i].second == hb.site) fasm_site = "DSP_" + std::to_string(i);
                }
                if (!fasm_site.empty()) {
                    hb.gate_name = sanitise(tile + "_" + fasm_site);
                    // Join the cut as well as naming the pair -- see the note
                    // on the DDR registers below.  A DSP's results are freed
                    // on both sides, so without this each side invents its own
                    // variable for the same pin and everything reading the
                    // product differs on the strength of the name alone.
                    for (const auto &dp : dsp::kDsp48e1) {
                        if (!dp.out) continue;
                        int w = dp.width ? dp.width : 1;
                        for (int b = 0; b < w; b++) {
                            std::string suffix =
                                std::string(":") + dp.name + "[" + std::to_string(b) + "]";
                            out.mem[hb.gate_name + suffix] = cv.first + suffix;
                        }
                    }
                }
            } else if (bel == "GTXE2_CHANNEL") {
                // The extraction emits the transceiver as a stub carrying its parallel outputs (see gtpins.hpp); name it as the tile
                // model does and join each output bit to the synthesis cell's, so the two cuts are one variable.
                hb.gate_name = sanitise(tile + "_GTXE2_CHANNEL");
                for (const auto &pc : cv.second.get("connections").members()) {
                    if (!gtx_channel_out(pc.first)) continue;
                    const auto &bits = pc.second.items();
                    for (size_t b = 0; b < bits.size(); b++)
                        out.mem[hb.gate_name + ":" + pc.first + "[" + std::to_string(b) + "]"] =
                            cv.first + ":" + pc.first + "[" + std::to_string(b) + "]";
                }
            } else if (bel == "IDDR" || bel == "ODDR" || bel == "ISERDESE2" ||
                       bel == "OSERDESE2") {
                // A SERDES sits in the same site as the DDR register it
                // replaces: an ISERDESE2 in the ILOGIC, an OSERDESE2 in the
                // OLOGIC, so the site lookup is identical.
                const bool is_in = (bel == "IDDR" || bel == "ISERDESE2");
                // The placement names the site as the device does,
                // ILOGIC_X0Y11; the FASM and the tile model name it by its
                // position within the tile, ILOGIC_Y1.  Enumerate the tile's
                // sites of that kind and index them, exactly as the RAMB18
                // halves above are, rather than parsing the Y and hoping.
                const char *pfx = is_in ? "ILOGIC_" : "OLOGIC_";
                const json::Value &tv = grid.get(tile);
                // Every name the site can go by in the extraction: one, except
                // in a _SING_ tile -- see below.
                std::vector<std::string> fasm_sites;
                if (!tv.isNull()) {
                    std::vector<std::pair<int, std::string>> at;
                    for (const auto &sv : tv.get("sites").members()) {
                        if (sv.first.rfind(pfx, 0) != 0) continue;
                        auto y = sv.first.rfind('Y');
                        if (y != std::string::npos)
                            at.push_back({atoi(sv.first.c_str() + y + 1), sv.first});
                    }
                    std::sort(at.begin(), at.end());
                    // ...and then INVERT the index.  The FASM name is not the
                    // position in the tile, it is its complement: nextpnr's
                    // write_iol_config spells it `1 - siteloc.y`, and the
                    // bitstreams agree -- in LIOI_TBYTESRC_X82Y8 the SD command
                    // pad sits at the lower site, ILOGIC_X0Y7, and both Vivado
                    // and nextpnr write its IDDR to ILOGIC_Y1.  Indexing
                    // straight names the OTHER site, which for a tile with one
                    // half in use reads as a hard block missing from the
                    // extraction, and for a tile with both in use silently
                    // pairs each cell with its neighbour.
                    if (at.size() == 2)
                        for (size_t i = 0; i < at.size(); i++)
                            if (at[i].second == hb.site)
                                fasm_sites.push_back(std::string(pfx) + "Y" + std::to_string(1 - i));
                    // A _SING_ tile holds one half, and which one it is depends
                    // on where the tile sits relative to its HCLK row rather
                    // than on anything here -- and the database's alias offset
                    // is no stand-in for it, since on some parts it names the
                    // other half.  But the tile holds ONE site of this kind, so
                    // there is no neighbour to pair the cell with by mistake,
                    // only a spelling to get wrong.  Name both spellings: the
                    // extraction takes the half from the FASM and instantiates
                    // exactly one of them, and a symbol the gate never produces
                    // pairs with nothing.
                    const bool sing_site = at.size() == 1 && at[0].second == hb.site;
                    if (sing_site)
                        for (const char *half : {"Y0", "Y1"})
                            fasm_sites.push_back(std::string(pfx) + half);
                }
                // An OLOGIC holds two registers and the synthesis spends a
                // cell on each: OUTFF on the data path, TFF on the tristate.
                // They share a site, so the site name alone collides -- and a
                // collision here is silent, two cells claiming one gate.  The
                // placement names the bel; use it.
                for (std::string fasm_site : fasm_sites) {
                    std::string bel_name = pv2.get("bel").asString();
                    const bool tristate_register = bel == "ODDR" && bel_name == "TFF";
                    if (tristate_register) fasm_site += "_TFF";
                    const std::string gate_name = sanitise(tile + "_" + fasm_site);
                    if (hb.gate_name.empty())
                        hb.gate_name = gate_name;
                    else
                        hb.gate_name_alt = gate_name;
                    // Naming the pair is not enough: the cut has to be joined
                    // too, the way a block RAM's data outputs are, or each
                    // side invents its own free variable for the same pin and
                    // everything the pad feeds differs on the strength of the
                    // name alone.
                    const std::vector<const char *> &outs =
                        bel == "IDDR"       ? kIddrOuts
                        : bel == "ODDR"     ? kOddrOuts
                        : bel == "ISERDESE2" ? kIserdesOuts
                                            : kOserdesOuts;
                    for (const char *pin : outs)
                        out.mem[gate_name + ":" + pin + "[0]"] =
                            cv.first + ":" + pin + "[0]";
                }
            }
            out.hard[cv.first] = hb;
        }
    }

    for (const auto &pv : place.members()) {
        if (pv.second.get("type").asString() != "SLICE_FFX")
            continue;
        std::string bel = pv.second.get("bel").asString();
        // AFF..DFF and A5FF..D5FF.  The second flip-flop of a column is
        // observable on the xMUX pin, the main one on xQ.
        if (bel.size() < 3 || bel[0] < 'A' || bel[0] > 'D') {
            out.skipped++;
            continue;
        }
        bool is5 = (bel[1] == '5');
        if (bel.substr(is5 ? 2 : 1) != "FF") {
            out.skipped++;
            continue;
        }
        const json::Value &cell = mod->get("cells").get(pv.first);
        if (cell.isNull()) {
            out.skipped++;
            continue;
        }
        const auto &q = cell.get("connections").get("Q").items();
        if (q.empty() || q[0].type != json::Type::Int) {
            out.skipped++;
            continue;
        }
        auto lb = label.find(q[0].asInt());
        if (lb == label.end()) {
            out.skipped++;
            continue;
        }
        std::string tile = pv.second.get("tile").asString();
        std::string site = pv.second.get("site").asString();
        auto pins = pins_for(tile, site);
        auto wire = pins.find(std::string(1, bel[0]) + (is5 ? "MUX" : "Q"));
        if (wire == pins.end()) {
            out.skipped++;
            continue;
        }
        out.net[tile + "/" + wire->second] = lb->second;
        {
            auto a = alt_label.find(q[0].asInt());
            if (a != alt_label.end()) out.alt[tile + "/" + wire->second] = a->second;
        }
        out.mapped++;
    }
    return out;
}

}  // namespace lvs
