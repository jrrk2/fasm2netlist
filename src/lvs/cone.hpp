// Netlist -> Boolean cone.
//
// Turns each register's next-state function, and each output port bit, into a
// BoolNet expression over primary inputs and register-state symbols.  The
// symbols are named after the NET a register drives, which is the whole
// mechanism by which two netlists get compared: give the matched registers
// the same net name on both sides and their cones are expressed over the same
// variables, so a miter between them asks the right question.  Nothing here
// discovers that correspondence -- it is an input.
#ifndef LVS_CONE_HPP
#define LVS_CONE_HPP

#include "lvs/boolnet.hpp"
#include "lvs/netlist.hpp"

#include <map>
#include <set>
#include <string>

namespace lvs {

class Cones
{
  public:
    // One memory's boundary: the signals that have to agree for its contents
    // to agree, and the symbols its reads produce.  This is what makes a RAM
    // checkable without naming anything inside it -- prove the boundary and
    // the contents follow, whatever either side calls them.
    struct MemPort
    {
        // One named group of boundary bits: a distributed RAM's read address,
        // a block RAM's ENARDEN.  Named rather than positional because the two
        // sides build their lists independently -- from a RAM64M on one side
        // and an xcol on the other -- so the only thing that can pair two
        // groups is what they are called, and a report has to be able to say
        // which one failed.
        struct Group
        {
            std::string what;
            std::vector<Lit> bits;         // low bit first
            // Bits the synthesis side left as x.  A memory port that is only
            // ever read has no write data to speak of, and yosys says so;
            // comparing the fabric's real signal against a don't-care asks a
            // question with no answer, so those bits are not obligations.
            std::vector<bool> dontcare;    // empty, or one flag per bit
        };
        std::string where;                 // instance, for the report only
        std::vector<Group> boundary;
        std::vector<std::string> out_sym;  // the cut symbol each data bit reads
        // What the memory starts out holding: INIT_xx/INITP_xx as canonical
        // hex, rows of all zeros left out.  A cut hides the contents from the
        // proof, so they are carried here and compared directly -- two block
        // RAMs with the same boundary and different contents are not the same
        // memory, and nothing else in this checker would notice.
        std::map<std::string, std::string> contents;
    };
    // Every memory port in this module, in a stable order.  Built on demand:
    // it evaluates cones, so it cannot run before construction finishes.
    const std::vector<MemPort> &mem_ports()
    {
        if (!mem_ports_built_) { mem_ports_built_ = true; collect_mem_ports(); }
        return mem_ports_;
    }
    // Give a memory's reads the symbols its counterpart uses.  This is the
    // whole of pairing: two memories are the same one when their reads are
    // the same variables, and what justifies saying so is that their
    // boundaries prove equal.
    void set_mem_cuts(const std::map<std::string, std::string> &cuts) { mem_cut_ = cuts; }

    // memory_as_state makes a writable column's 64 stored bits state
    // elements, so a design containing distributed RAM can be reasoned about
    // at all.  Off by default, and deliberately: it is only half of what a
    // COMPARISON needs.  The other side's RAM primitives have to become the
    // same state symbols too, and until they do this side merely grows 64
    // unmatched symbols and a 64-way mux per read -- strictly more work for
    // strictly no more proof.  See tests/lvs_memstate_test.cpp for what the
    // half that exists is proved to do.
    Cones(const Module &m, BoolNet &net,
          const std::map<std::string, std::string> &rename = {},
          bool memory_as_state = false);

    // Next-state of the register driving `state_name`, as a literal.
    Lit next_state(const std::string &state_name);
    // Value of an output port bit, e.g. ("led", 3).
    Lit output_bit(const std::string &port, int bit);
    // Any net, by name -- for comparing an internal node rather than a
    // register or a port.  Localising a difference means being able to ask
    // about the signals between them.
    Lit value_of(const std::string &net) { return eval_net(net, 0); }

    const std::set<std::string> &states() const { return states_; }
    // Every name this net answers to.  A net can be named more than once --
    // `assign \core.johnson[0] = \led_int[0]` makes both names the same wire
    // -- and the two sides of a comparison need not have picked the same one.
    std::set<std::string> synonyms(const std::string &net) const;
    const std::set<std::string> &free_nets() const { return free_nets_; }
    // How many combinational loops were broken with a constant.  A run
    // that broke any is a run in which some cone lost a dependency, so
    // a proof from it is conditional on those loops being unreachable.
    int loops_broken() const { return loops_seen_; }
    std::vector<std::pair<std::string, int>> output_bits() const;

  private:
    struct Driver
    {
        const Instance *inst;
        std::string pin;
    };

    Lit eval_net(const std::string &net_name, int depth);
    Lit eval_expr(const Expr &e, int depth);
    // One bit of a possibly-wide connection: a concatenation, a sized
    // constant, or a part select.  Carry logic is written as buses even in a
    // gate-level netlist, so bit-addressing them is not optional.
    Lit eval_bit(const Expr &e, int bit, int depth);
    Lit eval_cell_output(const Instance &inst, const std::string &pin, int depth);
    std::string resolve(std::string n) const;
    std::string n_for_output(const Instance &inst, const std::string &pin) const;
    Lit sym_state(const std::string &x);

    bool memory_as_state_ = false;
    std::set<std::string> grouped_;   // deep-RAM groups already given their port
    const Module &mod_;
    BoolNet &net_;
    std::map<std::string, Driver> driver_;   // net -> what drives it
    std::map<std::string, std::string> alias_;
    std::map<std::string, bool> const_net_;   // `assign n = 1'b0;` tie-offs
    std::map<std::string, const Instance *> ff_by_state_;
    // A memory column's storage is state too, one symbol per stored bit.  It
    // has no net of its own -- nothing in the netlist names bit 37 of a
    // distributed RAM -- so the symbol is built from the net the column reads
    // onto, which IS named and which both sides of a comparison can agree on.
    // mem_by_state_ maps such a symbol back to the column that holds it, and
    // mem_bit_ to which bit it is.
    std::map<std::string, const Instance *> mem_by_state_;
    std::map<std::string, int> mem_bit_;
    std::map<std::string, char> mem_port_;   // gold RAMs only: which port holds it
    std::vector<MemPort> mem_ports_;
    bool mem_ports_built_ = false;
    void collect_mem_ports();
    // The symbol a memory's data bit reads.  Paired memories are given the
    // same one, which is the whole of how a cut point works: downstream cones
    // then reference identical variables and cancel in the miter.
    std::map<std::string, std::string> mem_cut_;   // "inst/PORT/bit" -> symbol
    // A memory is cut per data-output BIT, so the symbol has to be found from
    // the net rather than from the pin: one pin can carry thirty-two of them.
    std::map<std::string, std::string> mem_out_;   // net -> its cut symbol
    static std::string mem_state_name(const std::string &anchor, int bit);
    std::string ram_anchor(const Instance &inst, const std::string &pin, int width) const;
    static std::string mem_cut_name(const std::string &ram, const std::string &pin, int bit);
    std::set<std::string> states_, free_nets_, inputs_;
    // Nets whose evaluation is on the stack.  A re-entry is a
    // combinational loop, and the constant it is broken with is
    // indistinguishable from a real zero once built -- so it is counted.
    std::set<std::string> in_progress_;
    int loops_seen_ = 0;
    std::vector<std::string> stack_;   // the descent, for naming a cycle
    std::map<std::string, Lit> memo_;
    std::map<std::string, std::string> rename_;   // this side's net -> shared symbol
    // resolved net -> every name that resolves to it, built on first ask
    mutable std::map<std::string, std::set<std::string>> syn_;
    mutable bool syn_built_ = false;
};

} // namespace lvs

#endif
