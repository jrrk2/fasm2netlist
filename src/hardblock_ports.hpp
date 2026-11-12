// The clock managers' and the ICAP's own interfaces, every pin the primitive has.
//
// Kept beside src/dsp_ports.hpp and for the same reason: the tile model, which emits these blocks from a bitstream, the equivalence
// checker, which cuts them at their boundary, and the register map, which pairs the two sides' cuts, must agree exactly about what the
// ports are.  A second copy would be a second opinion.
//
// None of the three is modelled.  What an MMCM does is a frequency and a phase, and what an ICAP does is read and write the
// configuration memory, and neither is a Boolean fact about this cycle.  So each is cut the way a DSP is: every output becomes a free
// variable that the placement pairs with the synthesis's own, and every input other than a clock becomes an obligation.  What is
// proved is that the two sides wired the same nets to the same pins of the same site -- a DRP write lands on the same address with the
// same data and enables, a configuration read is requested the same way -- and that whatever the block returns (DO, DRDY, LOCKED, O)
// reaches the same logic.  What is not proved is anything the block does internally, nor (for the clock managers) its configuration:
// the divisors and phases decide what frequency comes out, and that is not a thing this checker can state.
//
// Taken from the site pins prjxray records for the MMCME2_ADV, PLLE2_ADV and ICAP sites.  TESTIN, TESTOUT and TMUXOUT are site pins
// with no primitive port and are left out.  CLKOUT0..6, CLKIN1/2 and the like are discrete scalar ports, not buses.
#ifndef F2N_HARDBLOCK_PORTS_HPP
#define F2N_HARDBLOCK_PORTS_HPP

#include <cstring>
#include <iterator>
#include <string>

namespace hardblock {

struct Port {
	const char* name;
	int width;   // 0 = scalar
	bool out;
	bool clock;  // a clock input: assumed common to both sides, as a block RAM's or DSP's clock is, so not an obligation
};

inline constexpr Port kMmcme2[] = {
    // clock inputs and their selection
    {"CLKIN1", 0, false, true},   {"CLKIN2", 0, false, true},   {"CLKFBIN", 0, false, true},  {"CLKINSEL", 0, false, false},
    {"RST", 0, false, false},     {"PWRDWN", 0, false, false},
    // the dynamic reconfiguration port
    {"DADDR", 7, false, false},   {"DI", 16, false, false},     {"DEN", 0, false, false},     {"DWE", 0, false, false},
    {"DCLK", 0, false, true},
    // dynamic phase shift
    {"PSEN", 0, false, false},    {"PSINCDEC", 0, false, false}, {"PSCLK", 0, false, true},
    // outputs
    {"CLKOUT0", 0, true, false},  {"CLKOUT0B", 0, true, false}, {"CLKOUT1", 0, true, false},  {"CLKOUT1B", 0, true, false},
    {"CLKOUT2", 0, true, false},  {"CLKOUT2B", 0, true, false}, {"CLKOUT3", 0, true, false},  {"CLKOUT3B", 0, true, false},
    {"CLKOUT4", 0, true, false},  {"CLKOUT5", 0, true, false},  {"CLKOUT6", 0, true, false},
    {"CLKFBOUT", 0, true, false}, {"CLKFBOUTB", 0, true, false},
    {"LOCKED", 0, true, false},   {"CLKINSTOPPED", 0, true, false}, {"CLKFBSTOPPED", 0, true, false},
    {"DO", 16, true, false},      {"DRDY", 0, true, false},     {"PSDONE", 0, true, false},
};

// A PLL is an MMCM without the phase shifter, the inverted outputs, CLKOUT6 and the stop detectors.
inline constexpr Port kPlle2[] = {
    {"CLKIN1", 0, false, true},   {"CLKIN2", 0, false, true},   {"CLKFBIN", 0, false, true},  {"CLKINSEL", 0, false, false},
    {"RST", 0, false, false},     {"PWRDWN", 0, false, false},
    {"DADDR", 7, false, false},   {"DI", 16, false, false},     {"DEN", 0, false, false},     {"DWE", 0, false, false},
    {"DCLK", 0, false, true},
    {"CLKOUT0", 0, true, false},  {"CLKOUT1", 0, true, false},  {"CLKOUT2", 0, true, false},  {"CLKOUT3", 0, true, false},
    {"CLKOUT4", 0, true, false},  {"CLKOUT5", 0, true, false},  {"CLKFBOUT", 0, true, false},
    {"LOCKED", 0, true, false},   {"DO", 16, true, false},      {"DRDY", 0, true, false},
};

inline constexpr Port kIcape2[] = {
    {"I", 32, false, false}, {"CSIB", 0, false, false}, {"RDWRB", 0, false, false}, {"CLK", 0, false, true},
    {"O", 32, true, false},
};

struct Table {
	const Port* begin_;
	const Port* end_;
	const Port* begin() const { return begin_; }
	const Port* end() const { return end_; }
	bool empty() const { return begin_ == end_; }
};

// The table for a primitive, by the name either side gives it: the synthesis writes the BASE primitive when the design asks for no
// dynamic reconfiguration, and it has a subset of the same ports.  Empty for anything else.
inline Table ports_of(const std::string& type)
{
	if (type == "MMCME2_ADV" || type == "MMCME2_BASE") return {std::begin(kMmcme2), std::end(kMmcme2)};
	if (type == "PLLE2_ADV" || type == "PLLE2_BASE") return {std::begin(kPlle2), std::end(kPlle2)};
	if (type == "ICAPE2") return {std::begin(kIcape2), std::end(kIcape2)};
	return {nullptr, nullptr};
}

inline bool is_hardblock(const std::string& type) { return !ports_of(type).empty(); }

// The width of an output pin of this primitive (1 for a scalar), or 0 if it is not one.
inline int out_width(const std::string& type, const std::string& pin)
{
	for (const auto& p : ports_of(type))
		if (p.out && pin == p.name) return p.width ? p.width : 1;
	return 0;
}

} // namespace hardblock

#endif
