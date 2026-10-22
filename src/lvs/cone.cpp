#include <cstdio>
#include <iostream>
#include "lvs/cone.hpp"

#include "bram_ports.hpp"
#include "dsp_ports.hpp"
#include "gtpins.hpp"

#include <cstdlib>
#include <stdexcept>
#include <algorithm>

namespace lvs {

namespace {

// The _1 variants capture on the falling edge.  The proof has no notion of an edge (clocks are assumed common), so they are the same
// register as far as the next state goes; without them a negative-edge flop's output was a free variable on the synthesis side and a state
// on the extraction side.
const std::set<std::string> FF_TYPES = {"FDRE", "FDSE", "FDCE", "FDPE", "FDRE_1", "FDSE_1", "FDCE_1", "FDPE_1"};
// OBUFT: the output follows I; its tri-state enable T is not compared (a tri-stated pad does not hold a Boolean value, as for an inout).
const std::set<std::string> PASSTHROUGH = {"IBUF", "OBUF", "OBUFT", "BUFG", "IBUFDS", "OBUFDS"};
// A bidirectional buffer's O pin carries what the pad is receiving, which
// comes from the pad and not from anything inside the design.  Treating it as
// a connection to the IO pin lets it resolve to the port the constraints name,
// the same way an IBUF's O does.  The drive direction is a different question:
// what the design puts ON the pad is gated by T, and a tri-stated pad does not
// hold a boolean value, so an inout is not compared as an output.
const std::map<std::string, std::string> BIDIR_RECEIVE = {{"IOBUF", "IO"}, {"IOBUFDS", "IO"}};

// The wide multiplexers that join two LUT outputs into one wider function.
// The fabric side reaches them through a column's output mux, which the tile
// model already covers; the synthesis side instantiates them as cells, and
// leaving them out does not make one cone wrong -- it makes the net a MUXF
// drives look UNDRIVEN, so it becomes a free variable and every cone reading
// it differs from a counterpart that computed the value properly.
const std::set<std::string> WIDE_MUX = {"MUXF7", "MUXF8", "MUXF9"};

// Hard blocks with an output no Boolean model can produce, and the pins to cut
// at.  A PLL's LOCKED is the case in hand: it does not say anything about the
// design's signals, it says whether an analogue loop has settled, so neither
// netlist can compute it and the only sound thing is to give both sides the
// SAME free variable -- paired by the placement, exactly as a memory read is.
//
// What this does not check is the MMCM's configuration.  Nothing here could:
// the divisors decide what frequency comes out, and a frequency is not a
// Boolean fact.  The clock tree those outputs feed is assumed rather than
// reconstructed for the same reason (see the note on clock pins below), and
// this is the same assumption reaching one signal further.
//
// The DDR registers in the I/O logic are here for a different reason.  Both
// sides CAN compute them, but not in a way a combinational miter can compare:
// the second output is captured on the falling edge, and a proof with no
// notion of an edge cannot state that.  So both sides cut the same primitive
// at the same pins, and the placement pairs them -- which is what makes the
// two cuts cancel instead of becoming two unrelated free variables.  Leaving
// them unpaired does not weaken the proof, it destroys it: every cone
// downstream of a pad reads a symbol the other side has never heard of, and
// differs for that reason alone.
const std::map<std::string, std::set<std::string>> OPAQUE_OUT = {
    {"MMCME2_ADV", {"LOCKED"}},
    {"PLLE2_ADV", {"LOCKED"}},
    // The same block under the name synthesis gives it.  A bitstream only
    // knows the site, which is always the ADV superset, but yosys emits
    // whichever primitive the design instantiated -- and a design that asks
    // for no dynamic reconfiguration asks for the BASE one.  Cutting only
    // the ADV name cuts one side of the pair: the gate side becomes a free
    // variable and the gold side tries to evaluate through a clock manager,
    // so everything reading LOCKED differs for a reason that has nothing to
    // do with the design.  The placement pairs them by site either way.
    {"MMCME2_BASE", {"LOCKED"}},
    {"PLLE2_BASE", {"LOCKED"}},
    {"IDDR", {"Q1", "Q2"}},
    {"ODDR", {"Q"}},
    // A shift register's output is a function of what was shifted in over the last N clocks, which no cone of this cycle
    // states; it is cut as a distributed RAM's read is, and the extraction's SRL column reads the same symbol.
    {"SRL16E", {"Q"}},
    {"SRLC16E", {"Q", "Q15"}},
    {"SRLC32E", {"Q", "Q31"}},
    // A wide SERDES is cut at its boundary exactly as a DDR register is: its
    // serialisation is a function of time this proof has no notion of, so the
    // outputs become free variables and the parallel inputs (D1..D8, or the
    // captured Q1..Q8) become the obligations.  The synthesis carries the same
    // OSERDESE2/ISERDESE2 primitive with the same port names -- with no
    // SHIFTIN/SHIFTOUT cascade in any design seen here, each is a single cell
    // with a matching boundary -- so the two cuts cancel.  What is NOT checked
    // is the clock, the phase, or the bitslip, the same gap every cut carries.
    {"OSERDESE2", {"OQ", "TQ", "OFB", "TFB", "SHIFTOUT1", "SHIFTOUT2"}},
    {"ISERDESE2", {"O", "Q1", "Q2", "Q3", "Q4", "Q5", "Q6", "Q7", "Q8", "OFB",
                   "SHIFTOUT1", "SHIFTOUT2"}},
};
bool is_opaque_out(const std::string &type, const std::string &pin)
{
    auto it = OPAQUE_OUT.find(type);
    return it != OPAQUE_OUT.end() && it->second.count(pin) != 0;
}

// The synthesis-side distributed RAMs, and how wide one port's data is.  Each
// port is 64 stored bits either way -- 64 entries of one bit, or 32 of two --
// which is exactly one SLICEM column, and is why the two sides can be matched
// column for column.  The write address is port D's for both.
const std::map<std::string, int> RAM_PORTS = {{"RAM64M", 1}, {"RAM32M", 2}};
// The single-port ones, by address width: one column (32/64), a pair under
// an F7 (128) or the whole slice under the F8 (256).  One data bit, read and
// written at the same address, so the boundary is A, D and WE and the cut
// is O.  The fabric side is the same shape: a column, or a GROUP of columns
// the tile model marks and reads out on its mux (see xcol's DEPTH).
const std::map<std::string, int> RAM_SINGLE = {
    {"RAM32X1S", 5}, {"RAM64X1S", 6}, {"RAM128X1S", 7}, {"RAM256X1S", 8}};
// The dual-port ones, by address width: one memory, written and read at A on
// SPO and read at DPRA on DPO.  Packed, each port is a column of its own (the
// placement's <ram>/SP and <ram>/DP), so each is cut and paired as a port.
const std::map<std::string, int> RAM_DUAL = {{"RAM32X1D", 5}, {"RAM64X1D", 6}};
bool is_dual_out(const std::string &type, const std::string &pin)
{
    return RAM_DUAL.count(type) && (pin == "SPO" || pin == "DPO");
}

// The block RAMs.  Unlike a distributed RAM these are not modelled at all:
// their data outputs are cut and every one of their inputs becomes an
// obligation, so what gets proved is that the two sides wired the same nets to
// the same pins.  That leaves exactly one premise unchecked -- that the two
// have the same initial contents -- which is not a thing a boundary can say
// and is checked where it can be, against the bitstream, in
// tests/rtl/build_and_check.py.
bool is_bram(const std::string &t) { return t == "RAMB18E1" || t == "RAMB36E1"; }
// The DSP, cut the same way and for the same reason: nothing here models a
// multiply-accumulate, so its results are freed and its operands obliged.
bool is_dsp(const std::string &t) { return t == "DSP48E1"; }
bool is_gtx(const std::string &t) { return t == "GTXE2_CHANNEL"; }
// A block RAM's data outputs: the pins a cut turns into free variables.
bool bram_data_out(const std::string &pin)
{
    return pin == "DOADO" || pin == "DOBDO" || pin == "DOPADOP" || pin == "DOPBDOP";
}
// Its ports, widths and directions, from the one table the extractor uses.
// Calling the same pin by the same name on both sides is the whole mechanism:
// two block RAMs pair when the placement says they are in the same site, and
// what makes that pairing checkable is that "DIADI[7]" means the same thing
// either way.
std::vector<std::pair<std::string, int>> bram_ports(const std::string &type, bool out)
{
    std::vector<std::pair<std::string, int>> v;
    if (type == "RAMB36E1")
        for (const auto &p : bram::kRamb36) { if (p.out == out) v.push_back({p.port, p.width}); }
    else
        for (const auto &p : bram::kRamb18) { if (p.out == out) v.push_back({p.name, p.width}); }
    return v;
}

// Which stored bit port `p` reads at address `a` on data bit `d`: the address
// for a 64-deep port, and for a 32-deep one the two data bits are the two
// halves of the same column -- the same split the fabric makes between a
// column's O5 and O6 reads.  Used by the state model, which is the flagged
// alternative to cutting at the boundary.
[[maybe_unused]] int ram_bit(int width, int addr, int d) { return width == 1 ? addr : d * 32 + addr; }

// The tile model emitted by tileverilog.  One CLB column: a 6-input LUT read
// two ways, a main flip-flop, a second flip-flop, and the output mux.  Its
// selects arrive as string parameters, exactly as the FASM decoded them.
bool is_xcol(const std::string &t) { return t == "xcol"; }
std::string param_str(const Instance &i, const std::string &n, const std::string &dflt)
{
    auto v = i.param(n);
    if (!v) return dflt;
    std::string s = *v;
    if (s.size() >= 2 && s.front() == '"' && s.back() == '"') s = s.substr(1, s.size() - 2);
    return s;
}

// A LUT INIT as written in the netlist: 64'hf0f0..., 16'b0000...  Only the
// value matters here; the declared width is redundant with the pin count.
uint64_t parse_init(const std::string &text)
{
    auto tick = text.find('\'');
    std::string body = (tick == std::string::npos) ? text : text.substr(tick + 1);
    if (body.empty())
        return 0;
    char base = char(::tolower(body[0]));
    std::string digits = body.substr(base == 'b' || base == 'h' || base == 'o' || base == 'd' ? 1 : 0);
    std::string clean;
    for (char c : digits)
        if (c != '_')
            clean.push_back(c);
    int radix = base == 'b' ? 2 : base == 'o' ? 8 : base == 'd' ? 10 : 16;
    return std::strtoull(clean.c_str(), nullptr, radix);
}

std::string bit_name(const std::string &port, int bit) { return port + "[" + std::to_string(bit) + "]"; }

// How many bits a connection carries.  After `splitnets` every net is a
// scalar, so the only wide things left are constants, part selects and the
// concatenations that carry logic is written with.
int expr_width(const Expr &e)
{
    switch (e.kind) {
    case Expr::Kind::Const: {
        auto tick = e.const_text.find('\'');
        if (tick == std::string::npos || tick == 0)
            return 1;
        int w = std::atoi(e.const_text.substr(0, tick).c_str());
        return w > 0 ? w : 1;
    }
    case Expr::Kind::PartSel:
        return std::abs(e.range.msb - e.range.lsb) + 1;
    case Expr::Kind::Concat: {
        int w = 0;
        for (const auto &p : e.parts)
            w += expr_width(p);
        return w;
    }
    default:
        return 1;
    }
}

// The net carrying bit `bit` of a connection, or "" if that bit is not a
// plain net (a constant, say).  Used to record what an instance drives.
std::string net_of_bit(const Expr &e, int bit)
{
    switch (e.kind) {
    case Expr::Kind::Id:
        return bit == 0 ? e.name : bit_name(e.name, bit);
    case Expr::Kind::BitSel:
        return bit == 0 ? bit_name(e.name, e.index) : std::string();
    case Expr::Kind::PartSel:
        return bit_name(e.name, std::min(e.range.msb, e.range.lsb) + bit);
    case Expr::Kind::Concat: {
        // parts are written most significant first, so bit 0 is at the end
        int seen = 0;
        for (auto it = e.parts.rbegin(); it != e.parts.rend(); ++it) {
            int w = expr_width(*it);
            if (bit < seen + w)
                return net_of_bit(*it, bit - seen);
            seen += w;
        }
        return std::string();
    }
    default:
        return std::string();
    }
}

// Whether bit `bit` of a connection is one the synthesis has no opinion
// about: a pin it left unconnected, or a constant it wrote as x.  Both mean
// "this does not matter", and turning either into an obligation asks the
// prover a question with no answer.
bool bit_is_dontcare(const Expr &e, int bit)
{
    switch (e.kind) {
    case Expr::Kind::Unconnected:
        return true;
    case Expr::Kind::Const:
        return e.const_text.find('x') != std::string::npos ||
               e.const_text.find('z') != std::string::npos;
    case Expr::Kind::Concat: {
        int seen = 0;
        for (auto it = e.parts.rbegin(); it != e.parts.rend(); ++it) {
            int w = expr_width(*it);
            if (bit < seen + w)
                return bit_is_dontcare(*it, bit - seen);
            seen += w;
        }
        return true;   // past the end of the concatenation: nothing is there
    }
    default:
        // A named net that does not extend this far is not connected either.
        return net_of_bit(e, bit).empty();
    }
}

} // namespace

Lit Cones::sym_state(const std::string &x)
{
    auto r = rename_.find(x);
    if (r != rename_.end())
        return net_.input(r->second);
    // A stored bit is named after the net its column reads onto, so it
    // inherits that net's renaming: rename the column and its whole contents
    // follow.  Without this the two sides would agree on the register that
    // reads a memory and disagree on every bit inside it.
    auto at = x.rfind("$m");
    if (at != std::string::npos) {
        auto rr = rename_.find(x.substr(0, at));
        if (rr != rename_.end())
            return net_.input(rr->second + x.substr(at));
    }
    return net_.input(x);
}

std::string Cones::resolve(std::string n) const
{
    std::set<std::string> seen;
    while (alias_.count(n) && !seen.count(n)) {
        seen.insert(n);
        n = alias_.at(n);
    }
    return n;
}

Cones::Cones(const Module &m, BoolNet &net, const std::map<std::string, std::string> &rename,
             bool memory_as_state)
    : memory_as_state_(memory_as_state), mod_(m), net_(net), rename_(rename)
{
    for (const auto &p : m.ports)
        if (p.dir == PortDecl::Dir::Input || p.dir == PortDecl::Dir::Inout) {
            if (p.range.scalar)
                inputs_.insert(p.name);
            else
                for (int i = 0; i < p.range.width(); i++)
                    inputs_.insert(bit_name(p.name, i));
        }

    // `assign n = 1'b0;` is a tie-off, not a free net.  The extraction uses
    // these for genuinely-unrouted inputs, and missing them turns each one
    // into a free variable -- which makes any miter trivially satisfiable.
    for (const auto &a : m.assigns) {
        if (a.rhs.kind != Expr::Kind::Const)
            continue;
        bool v = parse_init(a.rhs.const_text) & 1;
        if (a.lhs.kind == Expr::Kind::Id)
            const_net_[a.lhs.name] = v;
        else if (a.lhs.kind == Expr::Kind::BitSel)
            const_net_[bit_name(a.lhs.name, a.lhs.index)] = v;
    }

    // `assign a = b;` is an alias, not logic
    for (const auto &a : m.assigns)
        if (a.lhs.kind == Expr::Kind::Id && a.rhs.kind == Expr::Kind::Id)
            alias_[a.lhs.name] = a.rhs.name;
        else if (a.lhs.kind == Expr::Kind::BitSel && a.rhs.kind == Expr::Kind::Id)
            alias_[bit_name(a.lhs.name, a.lhs.index)] = a.rhs.name;
        else if (a.lhs.kind == Expr::Kind::Id && a.rhs.kind == Expr::Kind::BitSel)
            alias_[a.lhs.name] = bit_name(a.rhs.name, a.rhs.index);
        else if (a.lhs.kind == Expr::Kind::BitSel && a.rhs.kind == Expr::Kind::BitSel)
            alias_[bit_name(a.lhs.name, a.lhs.index)] = bit_name(a.rhs.name, a.rhs.index);

    for (const auto &inst : m.instances) {
        // A column of a deeper distributed RAM (xcol's DEPTH > 64): the
        // group reads out on the mux named by GOUT, and that net is the cut.
        // Registered here, with the other memory reads, because the
        // register cones are built before the memory ports are collected
        // and a cut placed after a cone has been memoised cuts nothing.
        if (is_xcol(inst.type) && !memory_as_state_) {
            std::string gout = param_str(inst, "GOUT", "");
            std::string grp = param_str(inst, "GROUP", "");
            if (!gout.empty() && !grp.empty())
                mem_out_[gout] = mem_cut_name(grp, "O", 0);
        }
        // A carry cell drives eight nets from two four-bit pins, so its
        // outputs are recorded bit by bit; everything else here drives one
        // net from one pin.
        if (inst.type == "CARRY4") {
            for (const char *bus : {"O", "CO"}) {
                const Pin *p = inst.find_pin(bus);
                if (!p)
                    continue;
                for (int i = 0; i < 4; i++) {
                    std::string n = net_of_bit(p->conn, i);
                    if (!n.empty())
                        driver_[n] = Driver{&inst, bit_name(bus, i)};
                }
            }
            continue;
        }

        for (const auto &pin : inst.pins) {
            bool is_out = (is_xcol(inst.type) && (pin.name == "Q" || pin.name == "MUX" ||
                                                  pin.name == "O6" || pin.name == "O5" ||
                                                  pin.name == "CO")) ||
                          (FF_TYPES.count(inst.type) && pin.name == "Q") ||
                          (inst.type == "LUT6_2" && (pin.name == "O6" || pin.name == "O5")) ||
                          (inst.type.rfind("LUT", 0) == 0 && inst.type != "LUT6_2" && pin.name == "O") ||
                          (PASSTHROUGH.count(inst.type) && (pin.name == "O" || pin.name == "OB")) ||
                          (inst.type == "INV" && pin.name == "O") ||
                          (WIDE_MUX.count(inst.type) && pin.name == "O") ||
                          is_opaque_out(inst.type, pin.name) ||
                          (BIDIR_RECEIVE.count(inst.type) && pin.name == "O") ||
                          ((inst.type == "IDELAYE2" || inst.type == "ODELAYE2") && pin.name == "DATAOUT") ||
                          (RAM_PORTS.count(inst.type) && pin.name.rfind("DO", 0) == 0) ||
                          (RAM_SINGLE.count(inst.type) && pin.name == "O") ||
                          is_dual_out(inst.type, pin.name) ||
                          (is_bram(inst.type) && bram_data_out(pin.name)) ||
                          (is_dsp(inst.type) && dsp::is_data_out(pin.name.c_str())) ||
                          (is_gtx(inst.type) && gtx_channel_out(pin.name));
            if (!is_out)
                continue;
            // A memory's data output is a BUS, and every bit of it has to
            // claim its own net.  Registering one driver for the whole pin
            // leaves all but the first bit looking undriven -- a fresh free
            // variable with no counterpart on the other side -- and the pin's
            // connection is usually a concatenation, which has no single net
            // name at all, so nothing gets registered and every bit goes
            // free.  A sixteen-bit block RAM port and a two-bit RAM32M port
            // failed in exactly that same way; a one-bit RAM64M port did not,
            // which is what made it look like a block RAM problem.
            int mem_width = 0;
            if (is_opaque_out(inst.type, pin.name)) {
                mem_width = 1;
            } else if (is_bram(inst.type)) {
                for (const auto &p2 : bram_ports(inst.type, true))
                    if (p2.first == pin.name) mem_width = std::max(p2.second, 1);
            } else if (is_dsp(inst.type)) {
                for (const auto &p2 : dsp::kDsp48e1)
                    if (pin.name == p2.name) mem_width = std::max(p2.width, 1);
            } else if (is_gtx(inst.type)) {
                mem_width = std::max(expr_width(pin.conn), 1);
            } else if (RAM_SINGLE.count(inst.type) && pin.name == "O") {
                mem_width = 1;
            } else if (is_dual_out(inst.type, pin.name)) {
                mem_width = 1;
            } else if (!memory_as_state_ && RAM_PORTS.count(inst.type) &&
                       pin.name.rfind("DO", 0) == 0) {
                // Not under the state model: that one wants the whole pin, to
                // anchor 64 stored bits on the net the port reads onto.
                mem_width = RAM_PORTS.at(inst.type);
            }
            if (mem_width) {
                for (int b = 0; b < mem_width; b++) {
                    std::string bn = net_of_bit(pin.conn, b);
                    if (bn.empty()) continue;
                    driver_[bn] = Driver{&inst, pin.name};
                    mem_out_[bn] = mem_cut_name(inst.name, pin.name, b);
                }
                continue;
            }
            std::string n;
            if (pin.conn.kind == Expr::Kind::Id)
                n = pin.conn.name;
            else if (pin.conn.kind == Expr::Kind::BitSel)
                n = bit_name(pin.conn.name, pin.conn.index);
            else
                continue;
            driver_[n] = Driver{&inst, pin.name};
            if (FF_TYPES.count(inst.type)) {
                states_.insert(n);
                ff_by_state_[n] = &inst;
            }
            // an xcol column holds two registers: the main FF on Q, and the
            // second FF observable on MUX when the output mux selects it
            // A synthesis-side RAM port stores 64 bits, like the column it
            // will be matched against.  Anchor them on the read output the
            // fabric calls O6 -- the top data bit, which is the half a
            // column's O6 reads -- so the two sides name the same thing.
            if (memory_as_state_ && RAM_PORTS.count(inst.type) && pin.name.rfind("DO", 0) == 0) {
                int width = RAM_PORTS.at(inst.type);
                std::string anchor = ram_anchor(inst, pin.name, width);
                if (!anchor.empty())
                    for (int b = 0; b < 64; b++) {
                        std::string sn = mem_state_name(anchor, b);
                        states_.insert(sn);
                        mem_by_state_[sn] = &inst;
                        mem_bit_[sn] = b;
                        mem_port_[sn] = pin.name.size() > 2 ? pin.name[2] : 'A';
                    }
            }
            // A writable column stores 64 bits of state.  Enumerating them
            // here is what puts them in states(), so the prover asks for a
            // next-state function per stored bit the same way it does per
            // flip-flop -- there is no separate kind of thing.
            if (memory_as_state_ && is_xcol(inst.type) && pin.name == "O6" &&
                param_str(inst, "RAM", "0") != "0") {
                for (int b = 0; b < 64; b++) {
                    std::string sn = mem_state_name(n, b);
                    states_.insert(sn);
                    mem_by_state_[sn] = &inst;
                    mem_bit_[sn] = b;
                }
            }
            if (is_xcol(inst.type)) {
                if (pin.name == "Q" && param_str(inst, "FF_SRC", "none") != "none" &&
                    param_str(inst, "FF_THRU", "0").back() != '1') {
                    states_.insert(n);
                    ff_by_state_[n] = &inst;
                } else if (pin.name == "MUX" && param_str(inst, "OUTMUX", "none") == "5Q") {
                    states_.insert(n);
                    ff_by_state_[n] = &inst;
                }
            }
        }
    }
}

// Everything a cut hides: the contents AND the configuration of a primitive
// whose insides nothing here models.  Values are canonicalised so the two
// sides' spellings of the same thing compare equal -- 256'h00ab and 256'hab,
// TRUE and "TRUE", 32'd1 and 1.
static std::string hex_of_bits(const std::string &bits)
{
    std::string pad = bits;
    if (pad.size() % 4) pad.insert(0, 4 - pad.size() % 4, '0');
    std::string h;
    for (size_t i = 0; i < pad.size(); i += 4) {
        int v = 0;
        for (int k = 0; k < 4; k++) v = (v << 1) | (pad[i + k] == '1' ? 1 : 0);
        h += "0123456789abcdef"[v];
    }
    return h;
}

// A parameter's value as a canonical string, compared BY VALUE: 5'b00100, 5'h04, 5'd4 and 4 are the same number, and "READ_FIRST" and
// READ_FIRST the same word.  Numbers are hex without leading zeros; words are lowercase without quotes or underscores.
static std::string canon_value(std::string v)
{
    v.erase(std::remove(v.begin(), v.end(), '_'), v.end());
    v.erase(std::remove(v.begin(), v.end(), '"'), v.end());
    for (auto &c : v) c = char(std::tolower(c));
    auto strip = [](std::string h) {
        size_t nz = h.find_first_not_of('0');
        return nz == std::string::npos ? std::string("0") : h.substr(nz);
    };
    size_t tick = v.find('\'');
    if (tick != std::string::npos && tick + 2 <= v.size()) {
        const char base = v[tick + 1];
        std::string d = v.substr(tick + 2);
        if (d.find_first_of("xz") != std::string::npos) return d;          // a synthesis don't-care stays one
        if (base == 'b' && d.find_first_not_of("01") == std::string::npos) return strip(hex_of_bits(d));
        if (base == 'd' && d.size() <= 19 && d.find_first_not_of("0123456789") == std::string::npos) {
            char buf[32];
            snprintf(buf, sizeof(buf), "%llx", std::stoull(d));
            return buf;
        }
        return strip(d);                                                   // 'h (or anything else): the digits as written
    }
    if (!v.empty() && v.size() <= 19 && v.find_first_not_of("0123456789") == std::string::npos) {   // a plain decimal number
        char buf[32];
        snprintf(buf, sizeof(buf), "%llx", std::stoull(v));
        return buf;
    }
    if (!v.empty() && v.find_first_not_of("0123456789abcdefx") == std::string::npos) return strip(v);
    return v;
}

// Everything a cut hides: the contents AND the configuration of a primitive whose insides nothing here models.  Every parameter the
// instance names is kept, zero or not: a parameter the instance leaves out means the primitive's default, which is not always zero (a DSP's
// AREG is 1), so a dropped "0" and an absent row cannot be told apart and the comparison has to be able to see the difference.
static std::map<std::string, std::string> cut_config(const Instance &inst)
{
    std::map<std::string, std::string> out;
    for (const auto &pr : inst.params) {
        // Simulation-only: no bit, no hardware effect.
        if (pr.name == "SIM_DEVICE" || pr.name == "SIM_COLLISION_CHECK" || pr.name == "INIT_FILE") continue;
        std::string v = canon_value(pr.value);
        // The bitstream cannot tell the upper block of a cascaded pair from a RAM on its own: prjxray's RAM_EXTENSION_*_NONE_OR_UPPER is one bit,
        // set for LOWER and clear for both, so the extraction says NONE for an UPPER and the two are the same thing here.  Likewise MULTIPLY and
        // DYNAMIC: they give identical bitstreams (database FIXES.md, DSP48E1 USE_MULT).
        if ((pr.name == "RAM_EXTENSION_A" || pr.name == "RAM_EXTENSION_B") && v == "upper") v = "none";
        if (pr.name == "USE_MULT" && v == "dynamic") v = "multiply";
        out[pr.name] = v;
    }
    return out;
}

void Cones::collect_mem_ports()
{
    // A bus pin's bits, or -- where the primitive declares one pin per bit, as
    // the distributed RAMs do (A0..A5, DPRA0..DPRA5) -- those pins in turn
    auto bits_of = [&](const Instance &inst, const std::string &pin, int n) {
        std::vector<Lit> v;
        const Pin *p = inst.find_pin(pin);
        for (int i = 0; i < n; i++) {
            if (p) { v.push_back(eval_bit(p->conn, i, 0)); continue; }
            const Pin *pb = inst.find_pin(pin + std::to_string(i));
            v.push_back(pb ? eval_expr(pb->conn, 0) : LIT_FALSE);
        }
        return v;
    };
    auto lit_of = [&](const Instance &inst, const std::string &pin, Lit dflt) {
        const Pin *p = inst.find_pin(pin);
        return p ? eval_expr(p->conn, 0) : dflt;
    };
    auto group = [](const char *what, std::vector<Lit> bits) {
        MemPort::Group g;
        g.what = what;
        g.bits = std::move(bits);
        return g;
    };

    std::set<std::string> read_nets;   // nets something reads, for the dual-port RAMs below
    bool read_nets_built = false;
    for (const auto &inst : mod_.instances) {
        if (is_bram(inst.type)) {
            // A block RAM's boundary is its whole input side.  Listing it from
            // the port table rather than picking out the interesting pins is
            // the point: an unlisted input is one the cut quietly assumes
            // agrees, and there is no way to know from here which of REGCEB or
            // RSTRAMB a design leans on.
            MemPort mp;
            mp.where = inst.name;
            mp.contents = cut_config(inst);
            // A port of width 0 is a port the design does not have.  The
            // synthesis still writes its data pins, usually as literal zeros
            // (LiteX ties every unused input low), while an implementation is
            // free to leave the pins unrouted -- Vivado does, and an unrouted
            // pin reads the interconnect pull-up.  Asking the two to agree
            // about the data of a write that can never happen is not a
            // question about the design.  The address and enable of the
            // disabled port are still compared: a port the synthesis says is
            // disabled had better be one the bitstream leaves disabled too.
            auto width_of = [&](const char *name) -> uint64_t {
                auto v = inst.param(name);
                return v ? parse_init(*v) : 0;
            };
            bool no_write_a = inst.param("WRITE_WIDTH_A") && width_of("WRITE_WIDTH_A") == 0;
            bool no_write_b = inst.param("WRITE_WIDTH_B") && width_of("WRITE_WIDTH_B") == 0;
            auto write_data_unused = [&](const std::string &pin) {
                if (no_write_a && (pin == "DIADI" || pin == "DIPADIP" || pin == "WEA")) return true;
                if (no_write_b && (pin == "DIBDI" || pin == "DIPBDIP" || pin == "WEBWE")) return true;
                return false;
            };
            for (const auto &p : bram_ports(inst.type, false)) {
                // Not the clock.  The tile model does not reconstruct the
                // clock tree, it assumes it: with one BUFG in the design there
                // is only one thing a clock pin can be, and every clock pin is
                // joined to it.  Under that assumption the two sides cannot
                // disagree about a clock, so asking whether they do is not a
                // question -- and the gate's clock is a module input while the
                // synthesis's comes through an MMCM, so the two free variables
                // would differ by name alone.  This is the same reason a
                // flip-flop's C is never compared either.  --routed-clock
                // turns the assumption off; nothing here is a substitute.
                if (p.first.find("CLK") != std::string::npos) continue;
                int n = std::max(p.second, 1);
                MemPort::Group g;
                g.what = p.first;
                const Pin *pp = inst.find_pin(p.first);
                // What the boundary compares is the value the SITE sees, not
                // the value on the net: a control pin can be inverted on its
                // way in.  The synthesis says so with IS_<pin>_INVERTED, the
                // bitstream with a missing ZINV_<pin> tag, and the tile model
                // spends a real inverter on it -- so applying the parameter
                // here is what makes the two descriptions meet.  It is a
                // no-op on the fabric side, which carries no such parameter.
                bool inv = param_str(inst, "IS_" + p.first + "_INVERTED", "1'b0").back() == '1';
                // At width 1 a RAMB36E1 takes its write data on DIADI[0] AND DIADI[1] (and DIBDI likewise), and at width 9 the parity bit
                // on DIPADIP[0] and DIPADIP[1]: the two 18Kb halves each take their data from their own pin, and in these modes both
                // must carry it.  The synthesis names only bit 0; the bitstream, rightly, wires both.  So on the synthesis side the
                // second pin is the first (it is the hardware's requirement, not a claim the designer made), and the extraction's
                // second pin is still held to it -- a half that is not fed would show.
                const bool is36 = inst.type == "RAMB36E1";
                const int wa = int(width_of("WRITE_WIDTH_A")), wb = int(width_of("WRITE_WIDTH_B"));
                const bool second_pin_copies_first =
                    synthesis_side_ && is36 &&
                    ((p.first == "DIADI" && wa == 1) || (p.first == "DIBDI" && wb == 1) ||
                     (p.first == "DIPADIP" && wa == 9) || (p.first == "DIPBDIP" && wb == 9));
                // The parity pins exist only from width 9 up: at 1, 2 and 4 the primitive does not look at them, so a value on one is
                // not part of what the design does -- the synthesis ties them to 0 and the extraction leaves them on whatever wire
                // reaches the pin, and neither is a claim.
                const bool parity_unused = (p.first == "DIPADIP" && wa > 0 && wa < 9) || (p.first == "DIPBDIP" && wb > 0 && wb < 9);
                for (int b = 0; b < n; b++) {
                    const int sb = (second_pin_copies_first && b == 1) ? 0 : b;
                    Lit v = pp ? eval_bit(pp->conn, sb, 0) : LIT_FALSE;
                    g.bits.push_back(inv ? negate(v) : v);
                    // A pin the synthesis did not connect is one it has no
                    // opinion about, so it is not an obligation.  The fabric
                    // always has SOMETHING on the pin -- an unrouted one sits
                    // on the interconnect pull-up -- and demanding that the
                    // two agree would fail on pins neither design uses.
                    // The cascade inputs of an upper block are a dedicated wire from the lower block's outputs; nothing a fabric
                    // extraction can see, and not a net either side can name.  What decides the cascade is RAM_EXTENSION and address
                    // bit 15, which are compared.
                    // WEBWE[7:4] are the upper byte enables of the 72-bit simple-dual-port write; in TDP mode, at any width up to 36, they are
                    // not looked at, and nextpnr does not route them (the synthesis ties all eight to one net).
                    const bool webwe_upper_unused = is36 && p.first == "WEBWE" && b >= 4 &&
                                                    param_str(inst, "RAM_MODE", "TDP") != "SDP";
                    g.dontcare.push_back(webwe_upper_unused || !pp || bit_is_dontcare(pp->conn, sb) ||
                                         write_data_unused(p.first) || parity_unused || p.first.rfind("CASCADEIN", 0) == 0 ||
                                         (is36 && b == 15 && (p.first == "ADDRARDADDR" || p.first == "ADDRBWRADDR") &&
                                          param_str(inst, p.first == "ADDRARDADDR" ? "RAM_EXTENSION_A" : "RAM_EXTENSION_B", "NONE") != "LOWER" &&
                                          param_str(inst, p.first == "ADDRARDADDR" ? "RAM_EXTENSION_A" : "RAM_EXTENSION_B", "NONE") != "UPPER"));
                }
                mp.boundary.push_back(std::move(g));
            }
            for (const auto &p : bram_ports(inst.type, true)) {
                if (!bram_data_out(p.first)) continue;
                for (int b = 0; b < std::max(p.second, 1); b++)
                    mp.out_sym.push_back(mem_cut_name(inst.name, p.first, b));
            }
            if (!mp.out_sym.empty()) mem_ports_.push_back(std::move(mp));
            continue;
        }
        if (is_dsp(inst.type)) {
            // A DSP is cut exactly as a block RAM is, and until now nothing
            // compared what is inside it.  Its configuration decides what it
            // computes -- which operands INMODE selects, whether ALUMODE is
            // inverted, which registers are in the path -- so two DSPs with
            // the same boundary and different configuration are not the same
            // multiplier.
            MemPort mp;
            mp.where = inst.name;
            mp.dsp = true;
            mp.contents = cut_config(inst);
            // The per-pin inversions are applied to the pins below, so a row of their own would compare the same fact twice (and
            // spuriously: a synthesis that inverts a pin and a bitstream that inverts the net feeding it agree at the pin).
            for (const char *k : {"IS_ALUMODE_INVERTED", "IS_INMODE_INVERTED", "IS_OPMODE_INVERTED", "IS_CARRYIN_INVERTED"})
                mp.contents.erase(k);
            const bool dport = param_str(inst, "USE_DPORT", "FALSE") == "TRUE";
            for (const auto &p : dsp::kDsp48e1) {
                const Pin *pin = inst.find_pin(p.name);
                if (!pin)
                    continue;
                int w = std::max(p.width, 1);
                if (p.out) {
                    const std::string pn = p.name;
                    for (int b = 0; b < w; b++) {
                        std::string bn = net_of_bit(pin->conn, b);
                        if (!bn.empty()) {
                            mp.out_sym.push_back(bn);
                            if (pn == "PATTERNDETECT" || pn == "PATTERNBDETECT" || pn == "OVERFLOW" || pn == "UNDERFLOW") mp.patdet_used = true;
                        }
                    }
                } else {
                    const std::string name = p.name;
                    // The clock is assumed common to both sides, as for a block RAM (--routed-clock turns that off).
                    if (name == "CLK") continue;
                    MemPort::Group g;
                    g.what = name;
                    // The cascade inputs are a dedicated wire from the neighbouring DSP, not a net a fabric extraction can see, and
                    // D is not looked at when USE_DPORT is FALSE.  What chooses the cascade is OPMODE and the configuration, which
                    // are compared.
                    const bool cascade = name == "ACIN" || name == "BCIN" || name == "PCIN" || name == "CARRYCASCIN" ||
                                         name == "MULTSIGNIN";
                    const bool unused = cascade || (name == "D" && !dport);
                    // A control pin is compared as the site sees it: after IS_<pin>_INVERTED, per bit.
                    uint64_t invmask = 0;
                    if (name == "ALUMODE" || name == "INMODE" || name == "OPMODE" || name == "CARRYIN")
                        invmask = parse_init(param_str(inst, "IS_" + name + "_INVERTED", "0"));
                    for (int b = 0; b < w; b++) {
                        Lit v = eval_bit(pin->conn, b, 0);
                        g.bits.push_back((invmask >> b) & 1 ? negate(v) : v);
                        g.dontcare.push_back(unused || bit_is_dontcare(pin->conn, b));
                    }
                    mp.boundary.push_back(std::move(g));
                }
            }
            if (!mp.out_sym.empty()) mem_ports_.push_back(mp);
            continue;
        }

        if (inst.type == "SRL16E" || inst.type == "SRLC16E" || inst.type == "SRLC32E") {
            // Cut at its output: the boundary is the address it reads, the data it takes and the enable that shifts it, and the
            // initial contents are compared directly.  The clock is assumed common, as for a block RAM.
            const bool wide = inst.type == "SRLC32E";
            MemPort mp;
            mp.where = inst.name;
            if (wide) {
                mp.boundary.push_back(group("read address", bits_of(inst, "A", 5)));
            } else {
                std::vector<Lit> ra;
                for (int i = 0; i < 4; i++) ra.push_back(lit_of(inst, "A" + std::to_string(i), LIT_FALSE));
                mp.boundary.push_back(group("read address", std::move(ra)));
            }
            mp.boundary.push_back(group("write data", {lit_of(inst, "D", LIT_FALSE)}));
            mp.boundary.push_back(group("write enable", {lit_of(inst, "CE", LIT_TRUE)}));
            if (auto v = inst.param("INIT")) mp.contents["INIT"] = canon_value(*v);
            mp.out_sym.push_back(mem_cut_name(inst.name, "Q", 0));
            mem_ports_.push_back(std::move(mp));
            continue;
        }
        if (is_xcol(inst.type) && param_str(inst, "SRL", "0") != "0") {
            // The same boundary on the extraction's side.  A column holds one 32-deep register or two 16-deep ones: the upper
            // (O6) takes its data on the X bypass pin, the lower (O5) on the column's DI, and both read at A2..A5 with A1 high
            // (A6 high selects the upper half).  A 32-deep one reads on A2..A6.  The LUT's INIT holds each register bit twice,
            // at the A1-high position, which is where the register's own INIT is read from.
            const int srl = atoi(param_str(inst, "SRL", "0").c_str());
            const bool casc = param_str(inst, "SRLCASC", "0") != "0";
            const uint64_t lut = parse_init(param_str(inst, "INIT", "0"));
            const std::string name = param_str(inst, "MEMNAME", inst.name);
            for (int h = (srl == 2 ? 1 : 0); h >= 0; h--) {
                if (srl == 1 && h) continue;
                MemPort mp;
                mp.where = name + (srl == 2 ? (h ? " upper" : " lower") : "");
                const int nr = srl == 2 ? 4 : 5;
                std::vector<Lit> ra;
                for (int i = 0; i < nr; i++) {
                    const Pin *a = inst.find_pin("A" + std::to_string(i + 2));
                    ra.push_back(a ? eval_expr(a->conn, 0) : LIT_FALSE);
                }
                mp.boundary.push_back(group("read address", std::move(ra)));
                MemPort::Group wd = group("write data", {lit_of(inst, srl == 2 && h ? "DI2" : "DI", LIT_FALSE)});
                wd.dontcare.assign(1, casc);
                mp.boundary.push_back(std::move(wd));
                mp.boundary.push_back(group("write enable", {lit_of(inst, "WE", LIT_FALSE)}));
                uint64_t init = 0;
                const int n = srl == 2 ? 16 : 32, base = srl == 2 && h ? 32 : 0;
                for (int a = 0; a < n; a++)
                    if ((lut >> (base + 2 * a + 1)) & 1) init |= 1ull << a;
                char buf[32];
                snprintf(buf, sizeof(buf), "%llx", (unsigned long long)init);
                mp.contents["INIT"] = buf;
                mp.out_sym.push_back(mem_cut_name(name, "SRL", srl == 2 ? h : 0));
                mem_ports_.push_back(std::move(mp));
            }
            continue;
        }
        if (RAM_PORTS.count(inst.type)) {
            // One MemPort per data port; each is 64 stored bits, which is one
            // fabric column, which is what makes them pairable one to one.
            int width = RAM_PORTS.at(inst.type);
            int abits = (width == 1) ? 6 : 5;
            for (char port = 'A'; port <= 'D'; port++) {
                std::string dopin = std::string("DO") + port;
                if (!inst.find_pin(dopin)) continue;
                MemPort mp;
                mp.where = inst.name + " port " + port;
                mp.boundary.push_back(
                    group("read address", bits_of(inst, std::string("ADDR") + port, abits)));
                mp.boundary.push_back(group("write address", bits_of(inst, "ADDRD", abits)));
                {
                    MemPort::Group g =
                        group("write data", bits_of(inst, std::string("DI") + port, width));
                    const Pin *dp = inst.find_pin(std::string("DI") + port);
                    bool dc = !dp || (dp->conn.kind == Expr::Kind::Const &&
                                      dp->conn.const_text.find('x') != std::string::npos) ||
                              dp->conn.kind == Expr::Kind::Unconnected;
                    g.dontcare.assign(width, dc);
                    mp.boundary.push_back(std::move(g));
                }
                mp.boundary.push_back(group("write enable", {lit_of(inst, "WE", LIT_FALSE)}));
                for (int d = 0; d < width; d++)
                    mp.out_sym.push_back(mem_cut_name(inst.name, dopin, d));
                mem_ports_.push_back(std::move(mp));
            }
            continue;
        }
        if (RAM_DUAL.count(inst.type)) {
            // Two ports onto one memory, both written at A.  A port whose
            // output nothing reads is not one: the placer keeps no column for
            // it, and its write side is the other port's, compared there.
            if (!read_nets_built) {
                read_nets_built = true;
                auto note = [&](const Expr &e, const Instance *by, const std::string &pin) {
                    for (int b = 0, w = std::max(expr_width(e), 1); b < w; b++) {
                        std::string n = net_of_bit(e, b);
                        if (n.empty()) continue;
                        auto d = driver_.find(n);
                        const bool driving = d != driver_.end() && d->second.inst == by && d->second.pin == pin;
                        if (!driving) read_nets.insert(resolve(n));
                    }
                };
                for (const auto &i2 : mod_.instances)
                    for (const auto &p2 : i2.pins) note(p2.conn, &i2, p2.name);
                for (const auto &a : mod_.assigns) note(a.rhs, nullptr, "");
                for (const auto &pd : mod_.ports)
                    if (pd.dir != PortDecl::Dir::Input)
                        for (int b = 0; b < pd.range.width(); b++)
                            read_nets.insert(resolve(pd.range.scalar ? pd.name : bit_name(pd.name, std::min(pd.range.msb, pd.range.lsb) + b)));
            }
            int abits = RAM_DUAL.at(inst.type);
            for (const char *port : {"SPO", "DPO"}) {
                const Pin *op = inst.find_pin(port);
                const std::string on = op ? net_of_bit(op->conn, 0) : std::string();
                if (on.empty() || !read_nets.count(resolve(on))) continue;
                MemPort mp;
                mp.where = inst.name + " " + port;
                mp.boundary.push_back(group("read address", bits_of(inst, std::string(port) == "SPO" ? "A" : "DPRA", abits)));
                mp.boundary.push_back(group("write address", bits_of(inst, "A", abits)));
                {
                    MemPort::Group g = group("write data", {lit_of(inst, "D", LIT_FALSE)});
                    const Pin *dp = inst.find_pin("D");
                    g.dontcare.assign(1, !dp || bit_is_dontcare(dp->conn, 0));
                    mp.boundary.push_back(std::move(g));
                }
                mp.boundary.push_back(group("write enable", {lit_of(inst, "WE", LIT_FALSE)}));
                mp.out_sym.push_back(mem_cut_name(inst.name, port, 0));
                mem_ports_.push_back(std::move(mp));
            }
            continue;
        }
        if (RAM_SINGLE.count(inst.type)) {
            int abits = RAM_SINGLE.at(inst.type);
            MemPort mp;
            mp.where = inst.name;
            // One address for both: what it reads is what it writes.  The
            // fabric side names them separately -- its read climbs the mux
            // selects, its write takes the WA pins -- and both must agree
            // with this one, which is the whole of what makes the port
            // single.
            mp.boundary.push_back(group("read address", bits_of(inst, "A", abits)));
            mp.boundary.push_back(group("write address", bits_of(inst, "A", abits)));
            {
                MemPort::Group g = group("write data", {lit_of(inst, "D", LIT_FALSE)});
                const Pin *dp = inst.find_pin("D");
                g.dontcare.assign(1, !dp || bit_is_dontcare(dp->conn, 0));
                mp.boundary.push_back(std::move(g));
            }
            mp.boundary.push_back(group("write enable", {lit_of(inst, "WE", LIT_FALSE)}));
            mp.out_sym.push_back(mem_cut_name(inst.name, "O", 0));
            mem_ports_.push_back(std::move(mp));
            continue;
        }
        if (!is_xcol(inst.type) || param_str(inst, "RAM", "0") == "0") continue;
        // A column of a deeper group: the group is one port, cut at the mux
        // it reads out on, and any one of its columns carries the whole
        // boundary -- the read address up the selects, the write address up
        // WA7/WA8, the shared data and enable.  The first column met speaks
        // for the group; the rest are the same port and are not counted
        // again.
        {
            std::string grp = param_str(inst, "GROUP", "");
            int depth = atoi(param_str(inst, "DEPTH", "64").c_str());
            if (!grp.empty() && depth > 64) {
                if (grouped_.count(grp)) continue;
                grouped_.insert(grp);
                int abits = depth == 256 ? 8 : 7;
                MemPort mp;
                mp.where = grp;
                {
                    std::vector<Lit> ra;
                    for (int i = 0; i < 6; i++) {
                        const Pin *a = inst.find_pin("A" + std::to_string(i + 1));
                        ra.push_back(a ? eval_expr(a->conn, 0) : LIT_FALSE);
                    }
                    ra.push_back(lit_of(inst, "RA7", LIT_FALSE));
                    if (abits == 8) ra.push_back(lit_of(inst, "RA8", LIT_FALSE));
                    mp.boundary.push_back(group("read address", std::move(ra)));
                }
                {
                    std::vector<Lit> wa = bits_of(inst, "WA", 6);
                    wa.push_back(lit_of(inst, "WA7", LIT_FALSE));
                    if (abits == 8) wa.push_back(lit_of(inst, "WA8", LIT_FALSE));
                    mp.boundary.push_back(group("write address", std::move(wa)));
                }
                mp.boundary.push_back(group("write data", {lit_of(inst, "DI", LIT_FALSE)}));
                mp.boundary.push_back(group("write enable", {lit_of(inst, "WE", LIT_FALSE)}));
                mp.out_sym.push_back(mem_cut_name(grp, "O", 0));
                // ...and the cut itself: the group's mux output reads the
                // free symbol, so nothing descends into the columns.
                mem_ports_.push_back(std::move(mp));
                continue;
            }
        }
        bool small = param_str(inst, "RAM32", "0") != "0";
        int abits = small ? 5 : 6;
        MemPort mp;
        mp.where = inst.name;
        {
            std::vector<Lit> ra;
            for (int i = 0; i < abits; i++) {
                const Pin *a = inst.find_pin("A" + std::to_string(i + 1));
                ra.push_back(a ? eval_expr(a->conn, 0) : LIT_FALSE);
            }
            mp.boundary.push_back(group("read address", std::move(ra)));
        }
        mp.boundary.push_back(group("write address", bits_of(inst, "WA", abits)));
        {
            std::vector<Lit> wd{lit_of(inst, "DI", LIT_FALSE)};
            if (small) wd.push_back(lit_of(inst, "DI2", LIT_FALSE));
            mp.boundary.push_back(group("write data", std::move(wd)));
        }
        mp.boundary.push_back(group("write enable", {lit_of(inst, "WE", LIT_FALSE)}));
        for (int d = 0; d < (small ? 2 : 1); d++)
            mp.out_sym.push_back(mem_cut_name(inst.name, "DO", d));
        mem_ports_.push_back(std::move(mp));
    }
}

Lit Cones::eval_expr(const Expr &e, int depth)
{
    switch (e.kind) {
    case Expr::Kind::Unconnected:
        return LIT_FALSE;
    case Expr::Kind::Const: {
        // 1'b1 / 1'b0 -- anything wider has no business on a scalar pin
        uint64_t v = parse_init(e.const_text);
        return (v & 1) ? LIT_TRUE : LIT_FALSE;
    }
    case Expr::Kind::Id:
        return eval_net(e.name, depth);
    case Expr::Kind::BitSel:
        return eval_net(bit_name(e.name, e.index), depth);
    default:
        return LIT_FALSE;
    }
}

Lit Cones::eval_bit(const Expr &e, int bit, int depth)
{
    switch (e.kind) {
    case Expr::Kind::Unconnected:
        return LIT_FALSE;
    case Expr::Kind::Const:
        return ((parse_init(e.const_text) >> bit) & 1) ? LIT_TRUE : LIT_FALSE;
    case Expr::Kind::Concat: {
        int seen = 0;
        for (auto it = e.parts.rbegin(); it != e.parts.rend(); ++it) {
            int w = expr_width(*it);
            if (bit < seen + w)
                return eval_bit(*it, bit - seen, depth);
            seen += w;
        }
        return LIT_FALSE;
    }
    default: {
        std::string n = net_of_bit(e, bit);
        return n.empty() ? LIT_FALSE : eval_net(n, depth);
    }
    }
}

Lit Cones::eval_cell_output(const Instance &inst, const std::string &pin, int depth)
{
    auto in = [&](const char *p) {
        const Pin *q = inst.find_pin(p);
        return q ? eval_expr(q->conn, depth + 1) : LIT_FALSE;
    };

    if (PASSTHROUGH.count(inst.type)) {
        Lit i = in("I");
        return (pin == "OB") ? negate(i) : i;
    }

    if (inst.type == "INV")
        return negate(in("I"));

    // O = S ? I1 : I0.  Nothing subtler: the select is a real input like any
    // other, and both halves are evaluated because a miter needs the function,
    // not a simulation.
    if (WIDE_MUX.count(inst.type)) {
        Lit s = in("S"), i0 = in("I0"), i1 = in("I1");
        return net_.mk_or(net_.mk_and(s, i1), net_.mk_and(negate(s), i0));
    }

    {
        auto bd = BIDIR_RECEIVE.find(inst.type);
        if (bd != BIDIR_RECEIVE.end() && pin == "O")
            return in(bd->second.c_str());
    }

    // A delay line carries its input to its output unchanged.  It changes
    // WHEN a value arrives, never what it is, so for any boolean statement
    // about the design it is a wire -- and that is exactly the extent of what
    // checking a design containing one establishes.  DELAY_SRC says which of
    // the two inputs is being delayed.
    if (inst.type == "IDELAYE2" && pin == "DATAOUT")
        return in(param_str(inst, "DELAY_SRC", "IDATAIN") == "DATAIN" ? "DATAIN" : "IDATAIN");
    // The output delay takes ODATAIN (from the OSERDES or the fabric) to
    // DATAOUT, the pad's driver; the extraction has no cell for it either.
    if (inst.type == "ODELAYE2" && pin == "DATAOUT")
        return in("ODATAIN");

    if (inst.type == "CARRY4") {
        // Four stages of the same cell.  The carry into the chain is CYINIT
        // at the bottom of a column and CI above it; the unused one is tied
        // low, which is why the primitive can simply take both.  Then per
        // stage: the sum bit is the propagate signal against the incoming
        // carry, and the outgoing carry either propagates it or takes the
        // generate input DI -- the same mux the fabric's own column model
        // makes out of O6, CI and the O5/X choice.
        const Pin *sp = inst.find_pin("S"), *dp = inst.find_pin("DI");
        Lit carry = net_.mk_or(in("CI"), in("CYINIT"));
        for (int i = 0; i < 4; i++) {
            Lit s = sp ? eval_bit(sp->conn, i, depth + 1) : LIT_FALSE;
            Lit di = dp ? eval_bit(dp->conn, i, depth + 1) : LIT_FALSE;
            Lit sum = net_.mk_xor(s, carry);
            Lit co = net_.mk_or(net_.mk_and(s, carry), net_.mk_and(negate(s), di));
            if (pin == bit_name("O", i))
                return sum;
            if (pin == bit_name("CO", i))
                return co;
            carry = co;
        }
        return LIT_FALSE;
    }

    if (is_dual_out(inst.type, pin)) {
        std::string key = mem_cut_name(inst.name, pin, 0);
        auto c = mem_cut_.find(key);
        return net_.input(c == mem_cut_.end() ? key : c->second);
    }
    if (RAM_SINGLE.count(inst.type) && pin == "O") {
        std::string key = mem_cut_name(inst.name, "O", 0);
        auto c = mem_cut_.find(key);
        return net_.input(c == mem_cut_.end() ? key : c->second);
    }
    if (RAM_PORTS.count(inst.type) && pin.rfind("DO", 0) == 0) {
        // A cut point.  What a memory reads is not derived here at all: it is
        // a free symbol, and the paired memory on the other side is given the
        // SAME one.  Everything downstream then references identical
        // variables and cancels, so the proof reduces to the boundary --
        // which is the thing that can actually be checked, and the thing that
        // needs no agreement about what anything inside is called.
        std::string base = pin;
        int d = 0;
        auto br = pin.find('[');
        if (br != std::string::npos) { d = atoi(pin.c_str() + br + 1); base = pin.substr(0, br); }
        std::string key = mem_cut_name(inst.name, base, d);
        auto c = mem_cut_.find(key);
        return net_.input(c == mem_cut_.end() ? key : c->second);
    }

    if (is_xcol(inst.type)) {
        auto get_in = [&](int b) {                                  // b is 0-based
            const Pin *p = inst.find_pin("A" + std::to_string(b + 1));
            return p ? eval_expr(p->conn, depth + 1) : LIT_TRUE;     // unused inputs pull up
        };
        uint64_t init = parse_init(param_str(inst, "INIT", "0"));
        bool param_ram = param_str(inst, "RAM", "0") != "0";
        if ((pin == "O6" || pin == "O5") && param_str(inst, "SRL", "0") != "0") {
            // A shift register's read is a cut, like a RAM's: the free symbol the paired SRL16E/SRLC32E reads.
            const int srl = atoi(param_str(inst, "SRL", "0").c_str());
            std::string key = mem_cut_name(param_str(inst, "MEMNAME", inst.name), "SRL", srl == 2 && pin == "O6" ? 1 : 0);
            auto c = mem_cut_.find(key);
            return net_.input(c == mem_cut_.end() ? key : c->second);
        }
        if (pin == "O6" || pin == "O5") {
            int width = (pin == "O6") ? 6 : 5;
            if (!param_ram) {
                // A fixed LUT: the contents are a constant, so the read is a
                // truth table and no state is involved.
                //
                // Descend ONLY into the inputs that truth table depends on.  A
                // column holds two functions over the same five pins, and the
                // router feeds a pin because the O6 half wants it -- the O5
                // half is then wired to a signal it ignores.  Evaluating all
                // six regardless walks a path the logic does not have, and on
                // a real design that path closed a ring: B.O5 was routed
                // D.O6, D.O6 read B's mux, and the checker called it a
                // combinational loop and broke it with a constant.  Nothing
                // said so -- the constant is indistinguishable from a real
                // zero -- and every cone downstream of it quietly lost a
                // dependency.  On vc707-sdtest that deleted a counter's carry
                // and reported thirteen registers as differing.
                //
                // A don't-care input is not a dependency, so it is not a
                // reason to descend.  This is also the smaller network.
                uint64_t tt = (pin == "O6") ? init : (init & 0xffffffffull);

                // Restrict the table by any input that is TIED first.  A pin
                // held at VCC or GND selects half the table, and the other
                // inputs' relevance is decided by the half that survives, not
                // by the whole.  On vc707-litex a column had A6 tied high and
                // an A5 the full table depends on but the A6=1 half does not
                // -- and A5 was routed from the column's own output.  Judged
                // on the raw table that reads as a dependency, so the walk
                // followed it, came back to a net already on the stack, and
                // called a harmless piece of routing a combinational loop.
                // It oscillates only if the function inverts around it; this
                // one ignores the input entirely.
                std::vector<std::pair<int,bool>> tied;
                for (int b = 0; b < width; b++) {
                    const Pin *q = inst.find_pin("A" + std::to_string(b + 1));
                    if (!q) continue;
                    std::string n = resolve(net_of_bit(q->conn, 0));
                    auto c = const_net_.find(n);
                    if (c != const_net_.end()) tied.push_back({b, c->second});
                }
                for (auto [b, v] : tied) {
                    uint64_t out = 0;
                    for (uint32_t m = 0; m < (1u << width); m++) {
                        uint32_t src = v ? (m | (1u << b)) : (m & ~(1u << b));
                        if ((tt >> src) & 1) out |= 1ull << m;
                    }
                    tt = out;
                }

                std::vector<int> used;
                for (int b = 0; b < width; b++) {
                    bool dep = false;
                    for (uint32_t m = 0; m < (1u << width) && !dep; m++)
                        if (((tt >> m) & 1) != ((tt >> (m ^ (1u << b))) & 1))
                            dep = true;
                    if (dep) used.push_back(b);
                }
                uint64_t reduced = 0;
                for (uint32_t r = 0; r < (1u << used.size()); r++) {
                    uint32_t m = 0;
                    for (size_t k = 0; k < used.size(); k++)
                        if ((r >> k) & 1) m |= 1u << used[k];
                    if ((tt >> m) & 1) reduced |= 1ull << r;
                }
                std::vector<Lit> rins;
                rins.reserve(used.size());
                for (int b : used) rins.push_back(get_in(b));
                return net_.mk_lut(rins, reduced);
            }
            // The address is not evaluated before deciding what this read
            // IS.  A cut returns a free symbol and never looks at the address,
            // so descending into it first buys nothing and can cost a great
            // deal: the walk follows nets the answer does not depend on, and
            // where one of those leads back here the checker calls it a
            // combinational loop and breaks it with a constant.  The SD SoC
            // has its FIFOs in distributed RAM, which is why it showed 33 of
            // them where the design without the SD card showed none.
            if (!memory_as_state_) {
                // A cut point, the same as the synthesis side's RAM: what a
                // writable column reads is a free symbol, and the column it is
                // paired with gets the same one.  O6 and O5 are the two halves
                // of the one memory, so they are two different bits of it.
                // Which data bit this read is.  A 64-deep column has one --
                // O6, the whole address -- and matches a RAM64M port's single
                // DOx.  A 32-deep column has two halves, and they are the two
                // bits a RAM32M port calls DOx[1] and DOx[0].
                bool small = param_str(inst, "RAM32", "0") != "0";
                int d = small ? (pin == "O6" ? 1 : 0) : 0;
                std::string key = mem_cut_name(inst.name, "DO", d);
                auto c = mem_cut_.find(key);
                return net_.input(c == mem_cut_.end() ? key : c->second);
            }
            // A writable column: the contents are STATE, so the read is a mux
            // over the stored bits rather than over a constant. Built as a
            // balanced tree from the low address bit up, which keeps it the
            // same shape as mk_lut would have produced.  This is the one path
            // that genuinely reads the address, so this is where it is built.
            //
            // Only `width` of them.  A 32-deep column addresses on A1..A5 and
            // never reads A6, so walking all six follows a net the read does
            // not depend on -- and where that net leads back here the checker
            // calls it a combinational loop and substitutes a constant, which
            // is how a design that proved 2820/0 came to differ on 155 nets
            // after a placement change moved one wire.  Same rule as the
            // fixed-LUT path above: a pin the function does not use is not a
            // reason to descend.
            std::vector<Lit> sel;
            sel.reserve(width);
            for (int i = 0; i < width; i++) sel.push_back(get_in(i));
            std::string anchor = n_for_output(inst, "O6");
            std::vector<Lit> level;
            level.reserve(1u << width);
            for (int b = 0; b < (1 << width); b++)
                level.push_back(sym_state(mem_state_name(anchor, b)));
            for (int i = 0; i < width; i++) {
                std::vector<Lit> next;
                next.reserve(level.size() / 2);
                for (size_t j = 0; j + 1 < level.size(); j += 2)
                    next.push_back(net_.mk_or(net_.mk_and(negate(sel[i]), level[j]),
                                              net_.mk_and(sel[i], level[j + 1])));
                level.swap(next);
            }
            return level.front();
        }
        // The carry cell a column contributes to the chain.  O6 is the
        // propagate signal: it either passes the incoming carry along or
        // replaces it with the generate input, which is O5 or the X bypass
        // according to CY0.  XOR is the sum, and has no pin of its own -- it
        // reaches the world only through the flip-flop or the output mux.
        if (pin == "CO" || pin == "XOR") {
            Lit o6 = eval_cell_output(inst, "O6", depth);
            Lit ci = in("CI");
            if (pin == "XOR")
                return net_.mk_xor(o6, ci);
            Lit di = param_str(inst, "CY0", "X") == "O5" ? eval_cell_output(inst, "O5", depth)
                                                         : in("X");
            return net_.mk_or(net_.mk_and(o6, ci), net_.mk_and(negate(o6), di));
        }
        if (pin == "Q") {
            // A latch held open (see tileverilog): the column's Q IS its D
            // source, combinationally.
            if (param_str(inst, "FF_THRU", "0").back() == '1') {
                std::string src = param_str(inst, "FF_SRC", "none");
                if (src == "O6") return eval_cell_output(inst, "O6", depth);
                if (src == "O5") return eval_cell_output(inst, "O5", depth);
                if (src == "X") return in("X");
                if (src == "XOR") return eval_cell_output(inst, "XOR", depth);
                if (src == "CY") return eval_cell_output(inst, "CO", depth);
                if (src == "F7F8") { const Pin *fx = inst.find_pin("FX"); return fx ? eval_expr(fx->conn, depth) : LIT_FALSE; }
                return LIT_FALSE;
            }
            return sym_state(n_for_output(inst, "Q"));
        }
        if (pin == "MUX") {
            std::string sel = param_str(inst, "OUTMUX", "none");
            if (sel == "5Q") return sym_state(n_for_output(inst, "MUX"));
            if (sel == "O6") return eval_cell_output(inst, "O6", depth);
            if (sel == "O5") return eval_cell_output(inst, "O5", depth);
            if (sel == "XOR") return eval_cell_output(inst, "XOR", depth);
            if (sel == "CY") return eval_cell_output(inst, "CO", depth);
            if (sel == "F7" || sel == "F8") {
                const Pin *fx = inst.find_pin("FX");
                return fx ? eval_expr(fx->conn, depth) : LIT_FALSE;
            }
            return LIT_FALSE;
        }
        return LIT_FALSE;
    }

    if (inst.type == "LUT6_2" || inst.type.rfind("LUT", 0) == 0) {
        std::vector<Lit> ins;
        for (int i = 0;; i++) {
            const Pin *p = inst.find_pin("I" + std::to_string(i));
            if (!p)
                break;
            ins.push_back(eval_expr(p->conn, depth + 1));
        }
        auto init = inst.param("INIT");
        uint64_t val = init ? parse_init(*init) : 0;
        if (inst.type == "LUT6_2") {
            if (pin == "O5") {
                // O5 is the same INIT read with I5 held low: the low half
                std::vector<Lit> five(ins.begin(), ins.begin() + std::min<size_t>(5, ins.size()));
                return net_.mk_lut(five, val & 0xffffffffull);
            }
            return net_.mk_lut(ins, val);
        }
        return net_.mk_lut(ins, val);
    }

    throw std::runtime_error("cone: no model for cell type " + inst.type + " (pin " + pin + ")");
}

Lit Cones::eval_net(const std::string &raw, int depth)
{
    if (depth > 4096)
        throw std::runtime_error("cone: combinational loop at " + raw);
    std::string n = resolve(raw);

    auto it = memo_.find(n);
    if (it != memo_.end()) {
        if (in_progress_.count(n)) {
            if (loops_seen_++ < 2) {   // print a couple; count them all
                std::cerr << "  warning: combinational loop broken at " << n
                          << " -- its readers see a constant 0 here\n";
                size_t at = stack_.size();
                for (size_t i = 0; i < stack_.size(); i++)
                    if (stack_[i] == n) { at = i; break; }
                for (size_t i = at; i < stack_.size(); i++)
                    std::cerr << "      " << (i == at ? "-> " : "   ") << stack_[i] << "\n";
                std::cerr << "      back to " << n << "\n";
            }
        }
        return it->second;
    }

    Lit result;
    auto c = const_net_.find(n);
    if (c != const_net_.end()) {
        result = c->second ? LIT_TRUE : LIT_FALSE;
        memo_[n] = result;
        return result;
    }
    auto sym = [&](const std::string &x) {
        auto r = rename_.find(x);
        return net_.input(r == rename_.end() ? x : r->second);
    };
    if (states_.count(n)) {
        // a register output is a free symbol -- shared with the other side
        result = sym(n);
    } else if (inputs_.count(n)) {
        result = sym(n);
    } else {
        auto bo = mem_out_.find(n);
        if (bo != mem_out_.end()) {
            // A memory read is a cut point: whatever came out of the array is
            // a free variable, and the paired memory's read is renamed to the
            // same one so the two cancel wherever they are used.
            auto c2 = mem_cut_.find(bo->second);
            result = net_.input(c2 == mem_cut_.end() ? bo->second : c2->second);
            memo_[n] = result;
            return result;
        }
        auto d = driver_.find(n);
        if (d == driver_.end()) {
            // undriven: a free variable, and worth counting -- an undriven net
            // that exists on only one side is how a comparison goes wrong
            free_nets_.insert(n);
            result = sym(n);
        } else {
            // Break loops while descending.  A re-entry lands on this
            // constant and it is baked into whatever was being built, so a
            // false loop silently deletes a dependency rather than erroring:
            // count them and name the first few, because "the cone lost the
            // carry" and "the carry is genuinely zero" look identical once
            // the constant is in place.
            memo_[n] = LIT_FALSE;
            in_progress_.insert(n);
            stack_.push_back(n);
            result = eval_cell_output(*d->second.inst, d->second.pin, depth);
            stack_.pop_back();
            in_progress_.erase(n);
        }
    }
    memo_[n] = result;
    return result;
}

// Every name a net answers to.  Indexed on first use rather than scanned:
// the caller is a register correspondence, which asks this about every state
// on one side for every state on the other, and a scan of all the aliases per
// question turns a matching pass over a SoC into five minutes of walking the
// same chains again.  The index is the same answer, built once.
std::set<std::string> Cones::synonyms(const std::string &net) const
{
    if (!syn_built_) {
        syn_built_ = true;
        for (const auto &[from, to] : alias_) {
            (void)to;
            syn_[resolve(from)].insert(from);
        }
    }
    std::set<std::string> r{net};
    auto it = syn_.find(net);
    if (it != syn_.end())
        r.insert(it->second.begin(), it->second.end());
    return r;
}

// the net an xcol drives from a given pin, as a state symbol name
// A stored bit's state symbol.  Anchored on the column's read output so the
// name exists on both sides of a comparison: match the columns and the memory
// bits match with them, exactly as matching a register matches its state.
// A memory's read output, as a primary input: "ramname:pinname[bit]".
// One predictable pattern, used by both sides, so that pairing two memories is
// nothing more than agreeing on the ram name -- everything inside stays
// anonymous, which is the point.
std::string Cones::mem_cut_name(const std::string &ram, const std::string &pin, int bit)
{
    return ram + ":" + pin + "[" + std::to_string(bit) + "]";
}

// The net a RAM port reads its TOP data bit onto: DOx for a one-bit port,
// DOx[1] for a two-bit one.  That is the bit a fabric column reads on O6, and
// anchoring both sides there is what lets one rename match a whole memory.
std::string Cones::ram_anchor(const Instance &inst, const std::string &pin, int width) const
{
    const Pin *p = inst.find_pin(pin);
    if (!p) return {};
    if (width == 1)
        return p->conn.kind == Expr::Kind::Id ? p->conn.name
             : p->conn.kind == Expr::Kind::BitSel ? bit_name(p->conn.name, p->conn.index)
             : std::string();
    return net_of_bit(p->conn, 1);
}

std::string Cones::mem_state_name(const std::string &anchor, int bit)
{
    return anchor + "$m" + std::to_string(bit);
}

std::string Cones::n_for_output(const Instance &inst, const std::string &pin) const
{
    const Pin *p = inst.find_pin(pin);
    if (!p) return inst.name + "." + pin;
    if (p->conn.kind == Expr::Kind::Id) return p->conn.name;
    if (p->conn.kind == Expr::Kind::BitSel) return bit_name(p->conn.name, p->conn.index);
    return inst.name + "." + pin;
}

Lit Cones::next_state(const std::string &state_name)
{
    // A stored bit holds its value unless this cycle writes THIS bit: the
    // write enable is asserted and the write address selects it.  That is the
    // whole of a distributed RAM's state behaviour, and it is why the bits
    // belong in states() rather than in some parallel mechanism.
    auto mem = mem_by_state_.find(state_name);
    if (mem != mem_by_state_.end()) {
        const Instance &col = *mem->second;
        int bit = mem_bit_.at(state_name);
        auto pin_lit = [&](const char *p, Lit dflt) {
            const Pin *q = col.find_pin(p);
            return q ? eval_expr(q->conn, 0) : dflt;
        };
        Lit held = sym_state(state_name);
        Lit we = pin_lit("WE", LIT_FALSE);
        bool small = param_str(col, "RAM32", "0") != "0";

        // The address this bit answers to. 32-deep columns are two memories
        // sharing five address bits, so bit 5 picks the half rather than
        // forming part of the address, and each half takes its own data.
        int addr_bits = small ? 5 : 6;
        Lit sel = LIT_TRUE;
        for (int i = 0; i < addr_bits; i++) {
            const Pin *w = col.find_pin("WA");
            Lit a = w ? eval_bit(w->conn, i, 0) : LIT_FALSE;
            sel = net_.mk_and(sel, ((bit >> i) & 1) ? a : negate(a));
        }
        Lit di = pin_lit(small && (bit & 32) ? "DI2" : "DI", LIT_FALSE);
        Lit write = net_.mk_and(we, sel);
        return net_.mk_or(net_.mk_and(write, di), net_.mk_and(negate(write), held));
    }

    auto gram = mem_by_state_.find(state_name);
    if (gram != mem_by_state_.end() && RAM_PORTS.count(gram->second->type)) {
        // The synthesis side of the same statement.  Every port writes at
        // port D's address -- one write address for the whole primitive, which
        // is the slice's single write address seen from the other side.
        const Instance &ram = *gram->second;
        int width = RAM_PORTS.at(ram.type);
        int bit = mem_bit_.at(state_name);
        int abits = (width == 1) ? 6 : 5;
        int addr = (width == 1) ? bit : (bit & 31);
        int d = (width == 1) ? 0 : (bit >> 5);
        char port = mem_port_.count(state_name) ? mem_port_.at(state_name) : 'A';
        Lit held = sym_state(state_name);
        const Pin *wp = ram.find_pin("ADDRD");
        Lit sel = LIT_TRUE;
        for (int i = 0; i < abits; i++) {
            Lit a = wp ? eval_bit(wp->conn, i, 0) : LIT_FALSE;
            sel = net_.mk_and(sel, ((addr >> i) & 1) ? a : negate(a));
        }
        const Pin *wep = ram.find_pin("WE");
        Lit we = wep ? eval_expr(wep->conn, 0) : LIT_FALSE;
        const Pin *dip = ram.find_pin(std::string("DI") + port);
        Lit di = dip ? eval_bit(dip->conn, d, 0) : LIT_FALSE;
        Lit write = net_.mk_and(we, sel);
        return net_.mk_or(net_.mk_and(write, di), net_.mk_and(negate(write), held));
    }

    auto it = ff_by_state_.find(state_name);
    if (it == ff_by_state_.end())
        throw std::runtime_error("cone: no register drives " + state_name);
    const Instance &ff = *it->second;

    if (is_xcol(ff.type)) {
        auto pin_lit = [&](const char *p, Lit dflt) {
            const Pin *q = ff.find_pin(p);
            return q ? eval_expr(q->conn, 0) : dflt;
        };
        bool second = (n_for_output(ff, "MUX") == state_name);
        std::string src = param_str(ff, second ? "FF5_SRC" : "FF_SRC", "none");
        Lit d = LIT_FALSE;
        if (src == "O6") d = eval_cell_output(ff, "O6", 0);
        else if (src == "O5") d = eval_cell_output(ff, "O5", 0);
        else if (src == "X") d = pin_lit("X", LIT_FALSE);
        else if (src == "XOR") d = eval_cell_output(ff, "XOR", 0);
        else if (src == "CY") d = eval_cell_output(ff, "CO", 0);
        // The slice's wide multiplexer, built between columns by the tile
        // model and arriving on this pin.  Tying it to nought instead, which
        // is what this did before, is not a missing cone: it is a register
        // whose next state is a constant, and every cone reading it differs.
        else if (src == "F7F8") d = pin_lit("FX", LIT_FALSE);
        Lit ce = pin_lit("CE", LIT_TRUE);
        Lit sr = pin_lit("SR", LIT_FALSE);
        Lit q = sym_state(state_name);
        Lit next = net_.mk_or(net_.mk_and(ce, d), net_.mk_and(negate(ce), q));
        std::string srval = param_str(ff, second ? "FF5_SRVAL" : "FF_SRVAL", "1'b0");
        bool sv = !srval.empty() && srval.back() == '1';
        next = sv ? net_.mk_or(sr, next) : net_.mk_and(negate(sr), next);
        return next;
    }

    auto pin_lit = [&](const char *p, Lit dflt) {
        const Pin *q = ff.find_pin(p);
        return q ? eval_expr(q->conn, 0) : dflt;
    };

    Lit d = pin_lit("D", LIT_FALSE);
    Lit ce = pin_lit("CE", LIT_TRUE);
    Lit q = net_.input(state_name);
    // CE low holds the current value
    Lit next = net_.mk_or(net_.mk_and(ce, d), net_.mk_and(negate(ce), q));

    std::string ff_type = ff.type;
    if (ff_type.size() > 2 && ff_type.compare(ff_type.size() - 2, 2, "_1") == 0) ff_type.resize(ff_type.size() - 2);
    if (ff_type == "FDRE") {
        Lit r = pin_lit("R", LIT_FALSE);
        next = net_.mk_and(negate(r), next);
    } else if (ff_type == "FDSE") {
        Lit s = pin_lit("S", LIT_FALSE);
        next = net_.mk_or(s, next);
    } else if (ff_type == "FDCE") {
        Lit clr = pin_lit("CLR", LIT_FALSE);
        next = net_.mk_and(negate(clr), next);
    } else if (ff_type == "FDPE") {
        Lit pre = pin_lit("PRE", LIT_FALSE);
        next = net_.mk_or(pre, next);
    }
    return next;
}

int Cones::clock_inverted(const std::string &state) const
{
    auto it = ff_by_state_.find(state);
    if (it == ff_by_state_.end()) return -1;
    const Instance &ff = *it->second;
    if (is_xcol(ff.type)) return param_str(ff, "CLK_INV", "0").back() == '1' ? 1 : 0;
    const bool by_type = ff.type.size() > 2 && ff.type.compare(ff.type.size() - 2, 2, "_1") == 0;
    const bool by_param = param_str(ff, "IS_C_INVERTED", "0").back() == '1';
    return (by_type != by_param) ? 1 : 0;
}

bool Cones::clock_is_constant(const std::string &state) const
{
    auto it = ff_by_state_.find(state);
    if (it == ff_by_state_.end()) return false;
    const Instance &ff = *it->second;
    if (is_xcol(ff.type)) return false;
    const Pin *c = ff.find_pin("C");
    if (!c) return false;
    if (c->conn.kind == Expr::Kind::Const) return true;
    std::string n = net_of_bit(c->conn, 0);
    return !n.empty() && const_net_.count(resolve(n)) > 0;
}

std::string Cones::clock_source(const std::string &state) const
{
    auto it = ff_by_state_.find(state);
    if (it == ff_by_state_.end()) return "";
    const Instance &ff = *it->second;
    if (is_xcol(ff.type)) return param_str(ff, "CLK_SRC", "");
    const Pin *c = ff.find_pin("C");
    if (!c) return "";
    std::string n = net_of_bit(c->conn, 0);
    if (n.empty()) return "";
    auto d = driver_.find(n);
    if (d == driver_.end()) d = driver_.find(resolve(n));
    if (d == driver_.end() || !d->second.inst) return "";
    return d->second.inst->type.rfind("BUFG", 0) == 0 ? d->second.inst->name : std::string();
}

Lit Cones::output_bit(const std::string &port, int bit)
{
    for (const auto &p : mod_.ports)
        if (p.name == port && p.range.scalar)
            return eval_net(port, 0);
    return eval_net(bit_name(port, bit), 0);
}

std::vector<std::pair<std::string, int>> Cones::output_bits() const
{
    std::vector<std::pair<std::string, int>> r;
    for (const auto &p : mod_.ports)
        if (p.dir == PortDecl::Dir::Output) {
            if (p.range.scalar)
                r.emplace_back(p.name, -1);
            else
                for (int i = 0; i < p.range.width(); i++)
                    r.emplace_back(p.name, i);
        }
    return r;
}

} // namespace lvs
