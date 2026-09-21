#include "lvs/tileconfig.hpp"

#include <algorithm>
#include <fstream>
#include <iomanip>
#include <sstream>
#include <stdexcept>

namespace lvs {

const char *to_string(FFSrc s)
{
    switch (s) {
    case FFSrc::O6: return "O6";
    case FFSrc::O5: return "O5";
    case FFSrc::BypassX: return "X";
    case FFSrc::Xor: return "XOR";
    case FFSrc::MC31: return "MC31";
    case FFSrc::Wide: return "F7F8";
    default: return "CY";
    }
}
const char *to_string(FF5Src s) { return s == FF5Src::O5 ? "O5" : "X"; }
const char *to_string(PreCyInit s)
{
    switch (s) {
    case PreCyInit::Zero: return "0";
    case PreCyInit::One: return "1";
    case PreCyInit::AX: return "AX";
    case PreCyInit::CIN: return "CIN";
    default: return "none";
    }
}
const char *to_string(Di1Src s)
{
    switch (s) {
    case Di1Src::OwnI: return "own";
    case Di1Src::Chain: return "chain";
    default: return "DI";
    }
}
const char *to_string(OutMux s)
{
    switch (s) {
    case OutMux::None: return "none";
    case OutMux::O6: return "O6";
    case OutMux::O5: return "O5";
    case OutMux::Xor: return "XOR";
    case OutMux::Q5: return "5Q";
    case OutMux::Carry: return "CY";
    case OutMux::F7: return "F7";
    case OutMux::F8: return "F8";
    default: return "MC31";
    }
}

namespace {

std::vector<std::string> split(const std::string &s, char sep)
{
    std::vector<std::string> out;
    std::string cur;
    for (char c : s) {
        if (c == sep) { out.push_back(cur); cur.clear(); }
        else cur.push_back(c);
    }
    out.push_back(cur);
    return out;
}

std::string trim(std::string s)
{
    while (!s.empty() && isspace((unsigned char)s.front())) s.erase(s.begin());
    while (!s.empty() && isspace((unsigned char)s.back())) s.pop_back();
    return s;
}

// 64'b0101... or 64'hdead
std::optional<uint64_t> parse_bits(const std::string &v)
{
    auto tick = v.find('\'');
    if (tick == std::string::npos) return std::nullopt;
    char base = char(tolower(v[tick + 1]));
    std::string digits;
    for (size_t i = tick + 2; i < v.size(); i++)
        if (v[i] != '_') digits.push_back(v[i]);
    uint64_t r = 0;
    if (base == 'b') {
        for (char c : digits) { r = (r << 1) | uint64_t(c == '1'); }
    } else if (base == 'h') {
        r = std::strtoull(digits.c_str(), nullptr, 16);
    } else {
        return std::nullopt;
    }
    return r;
}

bool is_slice_site(const std::string &s) { return s.rfind("SLICEM_", 0) == 0 || s.rfind("SLICEL_", 0) == 0; }
bool is_iologic_site(const std::string &s)
{
    return s.rfind("OLOGIC_Y", 0) == 0 || s.rfind("ILOGIC_Y", 0) == 0 ||
           s.rfind("IDELAY_Y", 0) == 0;
}

// tile type from the tile name: CLBLM_R_X31Y135 -> CLBLM_R
std::string tile_type_of(const std::string &tile)
{
    auto p = tile.rfind("_X");
    return p == std::string::npos ? tile : tile.substr(0, p);
}

} // namespace

DesignConfig read_fasm(const std::string &path)
{
    std::ifstream in(path);
    if (!in) throw std::runtime_error("cannot open " + path);

    DesignConfig dc;
    std::string line;
    while (std::getline(in, line)) {
        auto hash = line.find('#');
        if (hash != std::string::npos) line = line.substr(0, hash);
        line = trim(line);
        if (line.empty()) continue;

        // FASM annotations: a whole line of `{ key = "value", ... }` carries no
        // feature (bit2fasm emits unknown bits this way), and a feature line may
        // carry a trailing annotation.  Neither is configuration.
        if (line[0] == '{') continue;
        auto brace = line.find('{');
        if (brace != std::string::npos) line = trim(line.substr(0, brace));
        if (line.empty()) continue;

        std::string feature = line, value;
        auto eq = line.find('=');
        if (eq != std::string::npos) {
            feature = trim(line.substr(0, eq));
            value = trim(line.substr(eq + 1));
        }

        auto parts = split(feature, '.');
        if (parts.size() < 2) { dc.unhandled.push_back(feature); continue; }
        const std::string &tile = parts[0];

        if (parts.size() >= 3 && is_iologic_site(parts[1])) {
            IoLogicConfig &io = dc.iologic[tile + "/" + parts[1]];
            io.tile = tile;
            io.tile_type = tile_type_of(tile);
            io.site = parts[1];
            io.is_output = parts[1][0] == 'O';
            io.is_delay = parts[1].rfind("IDELAY_Y", 0) == 0;
            std::string rest = feature.substr(tile.size() + parts[1].size() + 2);
            if (rest == "OQUSED") io.oq_used = true;
            else if (rest.rfind("OMUX.", 0) == 0) io.omux = rest.substr(5);
            else if (rest == "ZINV_D") io.d_inverted = false;
            // The tristate path is not the data path: a pad driven all the
            // time still configures it, and BUF is that "always on" setting.
            else if (rest == "OSERDES.DATA_RATE_TQ.BUF") {}
            // ...and neither is the inversion on it.  ZINV_T1 decides whether
            // the pad drives when T is high or low, which changes WHEN the pad
            // is driven and never WHAT it drives.  The data path is what this
            // model states, and it does not state the tristate -- so a pad whose
            // output enable is inverted passes here.  That is the same gap
            // DATA_RATE_TQ.BUF above already leaves, named rather than widened.
            else if (rest == "ZINV_T1" || rest == "ZINV_T2" ||
                     rest == "ZINV_T3" || rest == "ZINV_T4") {}
            // The tristate path can hold a REGISTER, though, and that is not a
            // gap that can be left: the synthesis spends a whole ODDR cell on
            // it, bound to the site's TFF bel beside the OUTFF the data path
            // uses.  Extract only the data register and the two sides disagree
            // by one cell per bidirectional pad -- six of them on an SD bus.
            else if (rest == "ODDR_TDDR.IN_USE") io.tddr_in_use = true;

            // ---- DDR registers in the I/O site -----------------------------
            // These say the site holds a register rather than a wire.  Recorded
            // rather than dropped, so the extractor can cut the site at its
            // boundary and instantiate the primitive -- see is_ddr_block().
            else if (rest == "IDDR.IN_USE") io.is_iddr = true;
            else if (rest == "OSERDES.DATA_RATE_OQ.DDR") io.is_oddr = true;
            // A wide SERDES wears the same DDR bits but is a different thing:
            // there is no single primitive whose boundary matches on the
            // synthesis side, so mark it and let is_ddr_block() refuse rather
            // than emit an ODDR that is not what the silicon holds.
            else if (rest.rfind("OSERDES.DATA_WIDTH.", 0) == 0) io.serdes_wide = true;
            // An ISERDESE2 spells its width through the interface mode, not a
            // DATA_WIDTH tag: NETWORKING.DDR.W8 for the 8:1 deserialiser LiteX
            // uses on DDR read data.  Both this and ISERDES.IN_USE mark the
            // site as a SERDES to be cut, not a wire.
            else if (rest.rfind("ISERDES.DATA_WIDTH.", 0) == 0) io.serdes_wide = true;
            else if (rest.rfind("ISERDES.NETWORKING.", 0) == 0) io.serdes_wide = true;
            else if (rest == "ISERDES.IN_USE") io.serdes_wide = true;
            // The rest configure a DDR register without changing which net
            // reaches which pin, which is all the boundary cut asserts: initial
            // and set/reset values, set/reset style, capture edge, the shared
            // ISERDES plumbing an IDDR sits inside, and the inversions.
            else if (rest == "IDDR_OR_ISERDES.IN_USE" || rest == "OSERDES.IN_USE" ||
                     rest == "ODDR_TDDR.IN_USE" || rest == "ODDR.SRUSED" ||
                     rest.rfind("ISERDES.MODE.", 0) == 0 ||
                     rest.rfind("ISERDES.NUM_CE.", 0) == 0 ||
                     rest.rfind("IFF.DDR_CLK_EDGE.", 0) == 0 ||
                     rest.rfind("ODDR.DDR_CLK_EDGE.", 0) == 0 ||
                     rest.rfind("IFF.SRTYPE.", 0) == 0 ||
                     rest.rfind("OSERDES.SRTYPE.", 0) == 0 ||
                     rest.rfind("OSERDES.TSRTYPE.", 0) == 0 ||
                     rest.rfind("IFF.ZINIT_Q", 0) == 0 ||
                     rest.rfind("IFF.ZSRVAL_Q", 0) == 0 ||
                     rest == "ZINIT_OQ" || rest == "ZINIT_TQ" ||
                     rest == "ZSRVAL_OQ" || rest == "ZSRVAL_TQ" ||
                     rest == "IFF.ZINV_C" || rest == "ZINV_CLK") {}
            // The counterpart of IDELMUXE3.P0 below: straight from the pad.
            else if (rest == "IDELMUXE3.P1") io.delayed_input = false;
            // The ILOGIC input mux: P0 takes the delayed input from the
            // IDELAY beside it rather than the pad's own D.
            else if (rest == "IDELMUXE3.P0") io.delayed_input = true;
            // How the delay is set up says nothing about the value passing
            // through it, only about when: a tap count, a performance mode,
            // whether it is in use at all.
            else if (io.is_delay && (rest == "IN_USE" || rest == "HIGH_PERFORMANCE_MODE" ||
                                     rest.rfind("IDELAY_TYPE_", 0) == 0 ||
                                     rest.rfind("IDELAY_VALUE", 0) == 0 ||
                                     rest.rfind("ZIDELAY_VALUE", 0) == 0 ||
                                     rest.rfind("ZFINEDELAY", 0) == 0)) {}
            else if (io.is_delay && rest == "DELAY_SRC_IDATAIN") io.delay_from_pad = true;
            else if (io.is_delay && rest == "DELAY_SRC_DATAIN") io.delay_from_pad = false;
            else io.unhandled.push_back(rest);
            continue;
        }

        if (parts.size() < 3 || !is_slice_site(parts[1])) {
            // routing PIPs and non-slice site config: kept verbatim, decoded
            // by whichever tile model owns them
            dc.other_tiles[tile].push_back(feature.substr(tile.size() + 1));
            if (!value.empty()) dc.other_values[tile][feature.substr(tile.size() + 1)] = value;
            continue;
        }

        const std::string &site = parts[1];
        std::string key = tile + "/" + site;
        SliceConfig &sc = dc.slices[key];
        sc.tile = tile;
        sc.tile_type = tile_type_of(tile);
        sc.site = site;

        // rejoin whatever follows tile.site
        std::string rest;
        for (size_t i = 2; i < parts.size(); i++) rest += (i > 2 ? "." : "") + parts[i];

        auto column = [&](char c) -> ColumnConfig & {
            ColumnConfig &cc = sc.columns[c];
            cc.col = c;
            return cc;
        };

        if (rest.rfind("PRECYINIT.", 0) == 0) {
            std::string sel = rest.substr(10);
            if (sel == "C0") sc.precyinit = PreCyInit::Zero;
            else if (sel == "C1") sc.precyinit = PreCyInit::One;
            else if (sel == "AX") sc.precyinit = PreCyInit::AX;
            else if (sel == "CIN") sc.precyinit = PreCyInit::CIN;
            else sc.unhandled.push_back(rest);
            continue;
        }
        if (rest.rfind("CARRY4.", 0) == 0) {
            std::string sel = rest.substr(7);
            // <col>CY0 -- the only CARRY4 feature the corpus shows
            if (sel.size() == 4 && sel[0] >= 'A' && sel[0] <= 'D' && sel.substr(1) == "CY0") {
                ColumnConfig &cc = column(sel[0]);
                cc.carry_used = true;
                cc.cy0_o5 = true;
            } else {
                sc.unhandled.push_back(rest);
            }
            continue;
        }
        if (rest == "FFSYNC") { sc.ffsync = true; continue; }
        if (rest == "NOCLKINV") { sc.clkinv = false; continue; }
        if (rest == "CLKINV") { sc.clkinv = true; continue; }
        if (rest == "LATCH") { sc.latch = true; continue; }
        if (rest == "SRUSEDMUX") { sc.srusedmux = true; continue; }
        if (rest == "CEUSEDMUX") { sc.ceusedmux = true; continue; }

        char c = rest.empty() ? '?' : rest[0];
        bool col_ok = (c >= 'A' && c <= 'D');
        std::string tail = col_ok ? rest.substr(1) : rest;

        if (col_ok && tail.rfind("LUT.INIT", 0) == 0) {
            ColumnConfig &cc = column(c);
            cc.lut_used = true;
            // prjxray writes the MINIMAL form of a multi-bit feature: the full
            // vector when it needs it, a trimmed range when the high bits are
            // zero, and a BARE FEATURE with no value at all when only one bit
            // is set:
            //     ALUT.INIT[63:0] = 64'b1111...
            //     ALUT.INIT[62:0] = 63'b1010...
            //     DLUT.INIT[54]
            // openXC7's writer always emits [63:0], so accepting only that was
            // enough until now.  A Vivado bitstream uses all three, and the
            // decoder reported 245 LUT features as "not modelled" -- which is
            // the dangerous kind of gap, because an unmodelled INIT bit is a
            // LUT whose extracted logic is quietly wrong rather than missing.
            //
            // Accept any [hi:lo] or [n], shift into place, and OR: several
            // bare bits can describe one LUT, and assigning would keep only
            // the last.
            size_t lb = tail.find('['), rb = tail.find(']');
            unsigned lo = 0;
            if (lb != std::string::npos && rb != std::string::npos && rb > lb) {
                std::string idx = tail.substr(lb + 1, rb - lb - 1);
                size_t colon = idx.find(':');
                try {
                    lo = unsigned(std::stoul(colon == std::string::npos
                                             ? idx : idx.substr(colon + 1)));
                } catch (...) { lo = 0; }
            }
            std::optional<uint64_t> bits =
                value.empty() ? std::optional<uint64_t>(1) : parse_bits(value);
            if (bits && lo < 64) {
                if (!cc.init) cc.init = 0;
                *cc.init |= (*bits) << lo;
            } else {
                sc.unhandled.push_back(rest + (value.empty() ? "" : " = " + value));
            }
        } else if (col_ok && tail == "FF.ZINI") { column(c).ff_init = 0; column(c).ff_used = true;
        } else if (col_ok && tail == "FF.ZRST") { column(c).ff_srval = 0; column(c).ff_used = true;
        } else if (col_ok && tail == "5FF.ZINI") { column(c).ff5_init = 0; column(c).ff5_used = true;
        } else if (col_ok && tail == "5FF.ZRST") { column(c).ff5_srval = 0; column(c).ff5_used = true;
        } else if (col_ok && tail.rfind("FFMUX.", 0) == 0) {
            ColumnConfig &cc = column(c);
            cc.ff_used = true;
            cc.ff_src_explicit = true;
            std::string sel = tail.substr(6);
            if (sel == "O6") cc.ff_src = FFSrc::O6;
            else if (sel == "O5") cc.ff_src = FFSrc::O5;
            else if (sel == std::string(1, c) + "X" || sel == "X") cc.ff_src = FFSrc::BypassX;
            else if (sel == "XOR") cc.ff_src = FFSrc::Xor;
            else if (sel == "MC31") cc.ff_src = FFSrc::MC31;
            else if (sel == "F7" || sel == "F8") cc.ff_src = FFSrc::Wide;
            else if (sel == "CY") cc.ff_src = FFSrc::Carry;
            else sc.unhandled.push_back(rest);
        } else if (col_ok && tail.rfind("5FFMUX.", 0) == 0) {
            ColumnConfig &cc = column(c);
            cc.ff5_used = true;
            cc.ff5_src_explicit = true;
            std::string sel = tail.substr(7);
            if (sel == "IN_A") cc.ff5_src = FF5Src::O5;
            else if (sel == "IN_B") cc.ff5_src = FF5Src::BypassX;
            else sc.unhandled.push_back(rest);
        } else if (col_ok && tail.rfind("OUTMUX.", 0) == 0) {
            ColumnConfig &cc = column(c);
            std::string sel = tail.substr(7);
            if (sel == "O6") cc.outmux = OutMux::O6;
            else if (sel == "O5") cc.outmux = OutMux::O5;
            else if (sel == "XOR") cc.outmux = OutMux::Xor;
            else if (sel == std::string(1, c) + "5Q" || sel == "5Q") { cc.outmux = OutMux::Q5; cc.ff5_used = true; }
            else if (sel == "CY") cc.outmux = OutMux::Carry;
            else if (sel == "F7") cc.outmux = OutMux::F7;
            else if (sel == "F8") cc.outmux = OutMux::F8;
            else if (sel == "MC31") cc.outmux = OutMux::MC31;
            else sc.unhandled.push_back(rest);
        } else if (col_ok && tail == "LUT.RAM") {
            column(c).ram = true;
        } else if (col_ok && tail == "LUT.SMALL") {
            column(c).ram_small = true;
        } else if (col_ok && tail.rfind("LUT.DI1MUX.", 0) == 0) {
            // <col>I selects the column's own write-data pin; anything else
            // is the chain that walks write data down from the column above.
            std::string sel = tail.substr(11);
            column(c).di1 = (sel == std::string(1, c) + "I") ? Di1Src::OwnI : Di1Src::Chain;
        } else if (rest == "WEMUX.CE") {
            sc.we_from_ce = true;
        } else if (rest == "WA7USED") {
            sc.wa7used = true;
        } else if (rest == "WA8USED") {
            sc.wa8used = true;
        } else {
            sc.unhandled.push_back(rest + (value.empty() ? "" : " = " + value));
        }
    }
    return dc;
}

void DesignConfig::dump(std::ostream &os) const
{
    for (const auto &[key, sc] : slices) {
        os << "slice " << key << " type=" << sc.tile_type
           << (sc.ffsync ? " ffsync" : " ffasync") << (sc.clkinv ? " clkinv" : "")
           << (sc.srusedmux ? " sr" : "") << (sc.ceusedmux ? " ce" : "");
        if (sc.precyinit != PreCyInit::None)
            os << " precyinit=" << to_string(sc.precyinit);
        if (sc.we_from_ce) os << " we=CE";
        if (sc.latch) os << " latch";
        if (sc.wa7used) os << " wa7";
        if (sc.wa8used) os << " wa8";
        os << "\n";
        for (const auto &[c, cc] : sc.columns) {
            os << "  col " << c;
            if (cc.init) {
                std::ostringstream h;
                h << std::hex << std::setw(16) << std::setfill('0') << *cc.init;
                os << " init=" << h.str();
            }
            if (cc.ff_used)
                os << " ff=" << (cc.ff_src_explicit ? to_string(cc.ff_src) : "O6(default)")
                   << ",init=" << cc.ff_init << ",srval=" << cc.ff_srval;
            if (cc.ff5_used)
                os << " ff5=" << (cc.ff5_src_explicit ? to_string(cc.ff5_src) : "O5(default)")
                   << ",init=" << cc.ff5_init << ",srval=" << cc.ff5_srval;
            os << " outmux=" << to_string(cc.outmux);
            if (cc.carry_used) os << " cy0=" << (cc.cy0_o5 ? "O5" : "X");
            if (cc.ram) os << " ram=" << (cc.ram_small ? "32" : "64") << " di1=" << to_string(cc.di1);
            os << "\n";
        }
        for (const auto &u : sc.unhandled)
            os << "  UNHANDLED " << u << "\n";
    }
    for (const auto &[tile, feats] : other_tiles) {
        std::vector<std::string> f = feats;
        std::sort(f.begin(), f.end());
        for (const auto &x : f)
            os << "tile " << tile << " " << x << "\n";
    }
    for (const auto &u : unhandled)
        os << "UNHANDLED " << u << "\n";
}

void DesignConfig::dump_gaps(std::ostream &os) const
{
    std::map<std::string, int> counts;
    for (const auto &[key, sc] : slices) {
        (void)key;
        for (const auto &u : sc.unhandled) {
            // count by shape, not by instance
            std::string shape;
            for (char ch : u) shape.push_back(isdigit((unsigned char)ch) ? '#' : ch);
            counts[shape]++;
        }
    }
    for (const auto &u : unhandled) counts["(non-tile) " + u]++;
    for (const auto &[shape, n] : counts)
        os << n << "\t" << shape << "\n";
    if (counts.empty())
        os << "no unhandled slice features\n";
}

} // namespace lvs
