// A structural Verilog netlist, and a flex/bison reader for it.
//
// The subset is the one a gate-level netlist actually uses: a module header
// (1995 or 2001 port style), net and port declarations with ranges, module
// instantiations with parameter overrides and named or ordered pin
// connections, and continuous assignments.  Rule names below deliberately
// follow ver_front/grammar.mly (moduleDecl, instDecl, instnameParen,
// cellpinItem, AssignOne, ...) so that growing this toward the full grammar
// is a matter of adding productions from that description rather than
// reshaping what is here.  Behaviour, ordering and never-silently-dropping
// are what matter for LVS: a pin this parser did not understand is an error,
// not a missing edge in a netlist graph that then compares equal by accident.
#ifndef LVS_NETLIST_HPP
#define LVS_NETLIST_HPP

#include <memory>
#include <optional>
#include <string>
#include <vector>

namespace lvs {

struct Range
{
    int msb = 0, lsb = 0;
    bool scalar = true;
    int width() const { return scalar ? 1 : (msb >= lsb ? msb - lsb + 1 : lsb - msb + 1); }
};

// A pin connection or assignment source.  Deliberately small: a gate-level
// netlist connects nets, bits of nets, constants and concatenations of those,
// and nothing else.
struct Expr
{
    enum class Kind
    {
        Unconnected,
        Id,      // \foo  or foo
        BitSel,  // foo[3]
        PartSel, // foo[7:0]
        Const,   // 1'b0, 64'hdead...
        Concat,  // {a, b[1], 1'b0}
    };
    Kind kind = Kind::Unconnected;
    std::string name;                 // Id / BitSel / PartSel
    int index = 0;                    // BitSel
    Range range;                      // PartSel
    std::string const_text;           // Const, verbatim as written
    std::vector<Expr> parts;          // Concat, in source order

    bool is_unconnected() const { return kind == Kind::Unconnected; }
};

struct PortDecl
{
    enum class Dir
    {
        Input,
        Output,
        Inout,
        None, // a plain wire/reg declaration
    };
    Dir dir = Dir::None;
    std::string name;
    Range range;
};

struct Param
{
    std::string name;   // empty for a positional override
    std::string value;  // verbatim, e.g. "64'hf0f0f0f0f0f0f0f0"
};

struct Pin
{
    std::string name;   // empty for a positional connection
    Expr conn;
};

struct Instance
{
    std::string type;   // cell type, e.g. LUT6_2
    std::string name;   // instance name, escaped form already stripped
    std::vector<Param> params;
    std::vector<Pin> pins;

    // Convenience for the common named-pin case.
    const Pin *find_pin(const std::string &pin) const
    {
        for (const auto &p : pins)
            if (p.name == pin)
                return &p;
        return nullptr;
    }
    std::optional<std::string> param(const std::string &pname) const
    {
        for (const auto &p : params)
            if (p.name == pname)
                return p.value;
        return std::nullopt;
    }
};

struct Assign
{
    Expr lhs, rhs;
};

struct Module
{
    std::string name;
    std::vector<PortDecl> ports;     // header order, direction filled in from declarations
    std::vector<PortDecl> nets;      // wire/reg declarations
    std::vector<Instance> instances;
    std::vector<Assign> assigns;
};

struct Netlist
{
    std::vector<Module> modules;
    const Module *find(const std::string &name) const
    {
        for (const auto &m : modules)
            if (m.name == name)
                return &m;
        return nullptr;
    }
};

// Throws std::runtime_error with file:line on a syntax error.  Never returns
// a partial parse.
Netlist parse_verilog_file(const std::string &path);
Netlist parse_verilog_string(const std::string &text, const std::string &origin = "<string>");
// A yosys-format JSON netlist (Verilator's --map-only-output, or yosys's
// write_json), as the Module the Verilog reader would build from that netlist
// split to single bits and written as Verilog.  json_netlist.cpp.
Netlist parse_json_netlist_file(const std::string &path);

} // namespace lvs

#endif
