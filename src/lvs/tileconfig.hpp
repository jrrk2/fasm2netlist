// Stage 1 of the tile-model converter: FASM features -> a tile's configuration,
// decoded into the same vocabulary the tile model takes as input.
//
// The point of this layer is that it makes NO inference about what a slice
// "means".  It reports which mux each select is set to and nothing more; what
// the resulting circuit looks like is the tile model's business.  Anything it
// does not recognise goes in `unhandled` rather than falling through to a
// default -- silently defaulting a mux select is how a wrong netlist gets
// produced that still looks plausible.
//
// The dump is canonical: fixed ordering, one fact per line, no addresses or
// timestamps, so two runs -- or two versions of the model -- can be diffed.
#ifndef LVS_TILECONFIG_HPP
#define LVS_TILECONFIG_HPP

#include <cstdint>
#include <map>
#include <optional>
#include <ostream>
#include <set>
#include <string>
#include <vector>

namespace lvs {

// The main flip-flop's D source, as `xcol`'s FFSRC names it.
enum class FFSrc { O6, O5, BypassX, Xor, MC31, Wide, Carry };
// The 5FF's D source: IN_A is the LUT's O5, IN_B the column's bypass pin.
enum class FF5Src { O5, BypassX };
// What the column's xMUX output carries.
enum class OutMux { None, O6, O5, Xor, Q5, Carry, F7, F8, MC31 };

// Where a memory column's write data comes from.  The DI1 mux is per column
// and its choices are the slice's own DI pins; a column with no DI1MUX feature
// takes the shared DI pin.
enum class Di1Src { DI, OwnI, Chain };

// Where the slice's carry chain starts.  Established from
// 017-clb-precyinit: one feature per value, 400 cases, no overlap.
enum class PreCyInit { None, Zero, One, AX, CIN };

const char *to_string(FFSrc s);
const char *to_string(FF5Src s);
const char *to_string(OutMux s);
const char *to_string(PreCyInit s);
const char *to_string(Di1Src s);

struct ColumnConfig
{
    char col = 'A';
    std::optional<uint64_t> init;   // xLUT.INIT[63:0]
    bool lut_used = false;

    bool ff_used = false;
    FFSrc ff_src = FFSrc::O6;       // only meaningful when ff_used
    bool ff_src_explicit = false;   // false = no FFMUX feature, i.e. the O6 default
    int ff_init = 1, ff_srval = 1;  // ZINI/ZRST are inverted senses

    bool ff5_used = false;
    FF5Src ff5_src = FF5Src::O5;
    bool ff5_src_explicit = false;
    int ff5_init = 1, ff5_srval = 1;

    OutMux outmux = OutMux::None;

    // CARRY4.<col>CY0 present selects O5 as the carry mux data input; absent
    // selects the column's X bypass.  Established from 013-clb-ncy0: 450
    // cases, present <-> clb_NCY0_O5, absent <-> clb_NCY0_MX.
    bool carry_used = false;
    bool cy0_o5 = false;

    // Distributed RAM.  ram makes this column's LUT storage writable; small
    // splits it into two 32-deep halves.  Established from 018-clb-ram and
    // 019-clb-ndi1mux.  A column with ram set reads exactly as it did before --
    // the read path IS the LUT read -- so the only new behaviour is the write
    // port, which is why the model can express it without a second cell.
    bool ram = false;
    bool ram_small = false;
    Di1Src di1 = Di1Src::DI;
};

struct SliceConfig
{
    std::string tile, tile_type, site;   // e.g. CLBLM_R_X31Y135, CLBLM_R, SLICEM_X0
    bool ffsync = false, clkinv = false, srusedmux = false, ceusedmux = false;
    // LATCH: every storage element in the slice is a latch, gated by CLK.
    bool latch = false;
    PreCyInit precyinit = PreCyInit::None;
    // Memory write control, shared by every column of the slice.
    bool we_from_ce = false;   // WEMUX.CE: the write enable is the CE pin, not WE
    bool wa7used = false;      // the write address extends past 6 bits...
    bool wa8used = false;      // ...and past 7
    std::map<char, ColumnConfig> columns;
    std::vector<std::string> unhandled;  // features this decoder does not model
};

// One OLOGIC or ILOGIC site: the register that sits between the fabric and a
// pad.  A design that only wants a wire still has to configure it, and what it
// configures is a bypass -- OMUX selecting D1 with OQ used on the way out, or
// an ILOGIC with nothing on the path but the optional inversion.  Anything
// else on these sites (a real output register, DDR, a SERDES, a delay in the
// data path) changes what the pad does and is reported rather than guessed at.
struct IoLogicConfig
{
    std::string tile, tile_type, site;   // e.g. RIOI3_X43Y61, OLOGIC_Y1
    bool is_output = false;              // OLOGIC (out) or ILOGIC (in)
    bool is_delay = false;               // IDELAY: the tap between pad and ILOGIC
    bool delayed_input = false;          // ILOGIC: IDELMUXE3 takes DDLY, not D
    bool delay_from_pad = true;          // IDELAY: DELAY_SRC is IDATAIN, not DATAIN
    bool oq_used = false;                // OQUSED: the pad is driven from OQ
    std::string omux;                    // what OMUX selects, "" if unset
    // ZINV_D says explicitly that the input is not inverted, but the bit does
    // not exist in every family's database -- virtex7's segbits_rioi.db has no
    // such line -- so its absence cannot be read as an inversion.  Nothing
    // seen so far inverts here; an ILOGIC that does would fail its proof,
    // which is the right way to find out rather than the wrong default.
    bool d_inverted = false;

    // A DDR register in the site, rather than a wire through it.  These are
    // cut at their boundary and instantiated as the primitive, exactly as a
    // block RAM is: what has to be right is which net reaches which pin, and
    // the synthesis side is cut on the same primitive with the same port
    // names, so the two cuts cancel.  Modelling the two edges instead would
    // put a negedge register into a proof that has no notion of one.
    bool is_iddr = false;                // ILOGIC: IDDR.IN_USE
    bool is_oddr = false;                // OLOGIC: OSERDES.DATA_RATE_OQ.DDR
    bool serdes_wide = false;            // ...but a SERDES, not a plain DDR
    bool tddr_in_use = false;            // OLOGIC: ODDR_TDDR.IN_USE, the T register

    std::vector<std::string> unhandled;  // anything implying more than a wire

    // True when the site holds a DDR register this model can cut at its
    // boundary.  A wide SERDES is not that: it has no single primitive with a
    // matching boundary on the synthesis side, so it stays unmodelled.
    bool is_ddr_block() const { return (is_iddr || is_oddr) && !serdes_wide && unhandled.empty(); }

    // True when this site is a plain connection and nothing more.
    bool is_bypass() const
    {
        if (!unhandled.empty()) return false;
        // A delay line is a wire as far as any boolean statement about the
        // design goes: it changes when a value arrives, never what it is.
        // That is the whole of what makes IDELAYE2 checkable here, and the
        // whole of what this check does not cover.
        if (is_delay) return true;
        // A DDR site is not a bypass and never claims to be; it is emitted as
        // the primitive instead of being dropped.
        if (is_iddr || is_oddr) return false;
        return is_output ? (oq_used && omux == "D1") : !d_inverted;
    }
};

struct DesignConfig
{
    std::map<std::string, SliceConfig> slices;      // key: tile + "/" + site
    std::map<std::string, IoLogicConfig> iologic;   // key: tile + "/" + site
    std::map<std::string, std::vector<std::string>> other_tiles; // tile -> features
    // The same features' values, where a feature had one: a block RAM's
    // INIT_xx/INITP_xx rows are 256-bit literals, and dropping them is what
    // left memory contents out of the extraction (tileverilog cut them at the
    // boundary because it had nothing to cut with).
    std::map<std::string, std::map<std::string, std::string>> other_values;
    std::vector<std::string> unhandled;

    // Canonical, sorted, one fact per line.
    void dump(std::ostream &os) const;
    // Only the parts no model covers yet, for measuring the gap.
    void dump_gaps(std::ostream &os) const;
};

// Reads a FASM file.  Routing features (tile-level PIPs) are kept verbatim
// against their tile; site features are decoded.
DesignConfig read_fasm(const std::string &path);

} // namespace lvs

#endif
