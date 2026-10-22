// A netlist from a yosys-format JSON file (the one Verilator's --map-only-output
// writes, or yosys's own write_json), built into the same Module the Verilog
// reader builds -- so the gold side of an LVS can be the synthesis's own
// output, with nothing converting it to Verilog first.
//
// The Module is the one `read_json; splitnets; write_verilog -norename` would
// have produced and the Verilog reader parsed: every net one bit wide and
// named "net" or "net[i]" (the bit's port, else the first name the JSON gives
// it), constants and parameters written as yosys writes them (32-bit numbers
// in decimal, others in hex, strings quoted), and an assignment from each of a
// bit's other names.  A bit no name claims gets "$json$<bit>".
#include <algorithm>
#include <fstream>
#include <map>
#include <sstream>
#include <stdexcept>

#include "json.hpp"
#include "lvs/netlist.hpp"

namespace lvs {
namespace {

std::string slurp(const std::string &path)
{
    std::ifstream f(path, std::ios::binary);
    if (!f) throw std::runtime_error("cannot open " + path);
    std::ostringstream ss;
    ss << f.rdbuf();
    return ss.str();
}

std::string bit_label(const std::string &name, size_t width, int64_t idx)
{
    return width == 1 && idx == 0 ? name : name + "[" + std::to_string(idx) + "]";
}

// A JSON parameter as yosys writes it in Verilog: a bit string (most
// significant first) is a sized constant -- decimal at 32 bits, hex otherwise,
// binary when it has x or z -- and anything else is a string
std::string param_text(const json::Value &v)
{
    if (v.type == json::Type::Int) return "32'd" + std::to_string(v.asInt());
    if (v.type == json::Type::Double) return std::to_string(v.asDouble());
    if (!v.isString()) return "0";
    std::string s = v.asString();
    const bool bits = !s.empty() && std::all_of(s.begin(), s.end(), [](char c) {
        return c == '0' || c == '1' || c == 'x' || c == 'z';
    });
    if (!bits) {
        // yosys marks a string that would read as bits with a trailing space
        if (!s.empty() && s.back() == ' ') s.pop_back();
        return "\"" + s + "\"";
    }
    const size_t w = s.size();
    if (s.find_first_of("xz") != std::string::npos) return std::to_string(w) + "'b" + s;
    if (w == 32) {
        uint64_t n = 0;
        for (char c : s) n = (n << 1) | uint64_t(c == '1');
        return "32'd" + std::to_string(n);
    }
    std::string hex;
    for (size_t end = w; end > 0;) {
        size_t start = end >= 4 ? end - 4 : 0;
        int nib = 0;
        for (size_t i = start; i < end; i++) nib = (nib << 1) | (s[i] == '1');
        hex.insert(hex.begin(), "0123456789abcdef"[nib]);
        end = start;
    }
    return std::to_string(w) + "'h" + hex;
}

Expr const_bit(const std::string &v)
{
    Expr e;
    e.kind = Expr::Kind::Const;
    e.const_text = v == "1" ? "1'h1" : v == "0" ? "1'h0" : "1'hx";
    return e;
}

Expr id(const std::string &name)
{
    Expr e;
    e.kind = Expr::Kind::Id;
    e.name = name;
    return e;
}

Module build_module(const std::string &mname, const json::Value &mod)
{
    Module m;
    m.name = mname;
    std::map<int64_t, std::string> canon;       // bit -> its one name
    std::vector<std::pair<std::string, int64_t>> aliases;

    // Ports first: a port's name is the bit's name, as in the Verilog, where
    // the port wire is the one the instances connect to
    for (const auto &pv : mod.get("ports").members()) {
        const auto &bits = pv.second.get("bits").items();
        PortDecl pd;
        const std::string dir = pv.second.get("direction").asString();
        pd.dir = dir == "input" ? PortDecl::Dir::Input : dir == "output" ? PortDecl::Dir::Output : PortDecl::Dir::Inout;
        pd.name = pv.first;
        if (bits.size() > 1) pd.range = Range{int(bits.size()) - 1, 0, false};
        m.ports.push_back(pd);
        for (size_t i = 0; i < bits.size(); i++) {
            if (bits[i].type != json::Type::Int) continue;
            canon.emplace(bits[i].asInt(), bit_label(pv.first, bits.size(), int64_t(i)));
        }
    }
    // Then the named signals, in the JSON's order: the first name a bit has
    // is the one the register map (regmap.cpp) labels it with, too
    for (const auto &nn : mod.get("netnames").members()) {
        const auto &bits = nn.second.get("bits").items();
        int64_t offset = nn.second.get("offset").isNull() ? 0 : nn.second.get("offset").asInt();
        const bool upto = !nn.second.get("upto").isNull() && nn.second.get("upto").asInt() != 0;
        for (size_t i = 0; i < bits.size(); i++) {
            if (bits[i].type != json::Type::Int) continue;
            const int64_t b = bits[i].asInt();
            const int64_t idx = offset + (upto ? int64_t(bits.size()) - 1 - int64_t(i) : int64_t(i));
            const std::string nm = bits.size() == 1 && offset == 0 ? nn.first : nn.first + "[" + std::to_string(idx) + "]";
            if (!canon.emplace(b, nm).second && canon.at(b) != nm) aliases.emplace_back(nm, b);
        }
    }
    auto bit_expr = [&](const json::Value &b) {
        if (b.type != json::Type::Int) return const_bit(b.asString());
        auto it = canon.find(b.asInt());
        if (it == canon.end()) it = canon.emplace(b.asInt(), "$json$" + std::to_string(b.asInt())).first;
        return id(it->second);
    };
    for (const auto &cv : mod.get("cells").members()) {
        Instance inst;
        inst.type = cv.second.get("type").asString();
        inst.name = cv.first;
        for (const auto &p : cv.second.get("parameters").members()) inst.params.push_back(Param{p.first, param_text(p.second)});
        for (const auto &c : cv.second.get("connections").members()) {
            const auto &bits = c.second.items();
            Pin pin;
            pin.name = c.first;
            if (bits.size() == 1) {
                pin.conn = bit_expr(bits[0]);
            } else if (!bits.empty()) {
                pin.conn.kind = Expr::Kind::Concat;
                for (size_t i = bits.size(); i-- > 0;) pin.conn.parts.push_back(bit_expr(bits[i]));  // most significant first
            }
            inst.pins.push_back(std::move(pin));
        }
        m.instances.push_back(std::move(inst));
    }
    // Every bit a wire of its own, as splitnets leaves it
    for (const auto &kv : canon) {
        PortDecl w;
        w.name = kv.second;
        m.nets.push_back(w);
    }
    for (const auto &a : aliases) {
        PortDecl w;
        w.name = a.first;
        m.nets.push_back(w);
        m.assigns.push_back(Assign{id(a.first), id(canon.at(a.second))});
    }
    return m;
}

} // namespace

Netlist parse_json_netlist_file(const std::string &path)
{
    json::Value root = json::parse(slurp(path));
    Netlist nl;
    for (const auto &kv : root.get("modules").members()) {
        // a black box's declaration carries no cells and is not a netlist
        if (!kv.second.get("attributes").get("blackbox").isNull()) continue;
        nl.modules.push_back(build_module(kv.first, kv.second));
    }
    if (nl.modules.empty()) throw std::runtime_error(path + ": no modules");
    return nl;
}

} // namespace lvs
