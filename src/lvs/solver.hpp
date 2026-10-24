// Run an external solver over a miter written in a standard format.
//
// The solver is a command, not a link-time dependency: whatever reads DIMACS
// or SMT-LIB 2 on the command line can be dropped in without recompiling.
#ifndef LVS_SOLVER_HPP
#define LVS_SOLVER_HPP

#include <cstdint>
#include <memory>
#include <string>

namespace lvs {

class BoolNet;
using Lit = uint32_t;

enum class Format
{
    Dimacs,
    SmtLib2,
};

enum class Result
{
    Unsat, // the miter is unsatisfiable: the two sides agree
    Sat,   // a counterexample exists: they do not
    Unknown,
};

struct Solver
{
    // e.g. {"z3", Format::SmtLib2} or {"cadical", Format::Dimacs}.  The file
    // is passed as the last argument.
    std::string command;
    Format format;

    // Defaults to the solver already assumed by this project, reached through
    // a file rather than an API so that swapping it is a flag.
    static Solver z3() { return Solver{"z3", Format::SmtLib2}; }
};

// Writes `text` to a temporary file, runs the solver on it, and classifies
// stdout.  Recognises both the SAT-competition ("s SATISFIABLE") and SMT-LIB
// ("sat") answer conventions, so one parser covers both formats.
Result run_solver(const Solver &solver, const std::string &text);

// One solver, many questions about one network.
//
// An LVS run asks the same shape of question once per register: is THIS
// literal of the shared network satisfiable?  The network itself -- both
// designs' logic, and everything the two have in common -- is the same every
// time, so a session states it once and asks each question as an assumption
// on top.  That is what the file-per-question route cannot do: it re-states
// the whole problem, and the solver re-reads it, for every register.
//
// The network may grow between calls (cones are built on demand), and a
// session picks up whatever has been added since it last looked.
class Session
{
  public:
    virtual ~Session() = default;
    // Satisfiable => Sat, and the two sides differ; unsatisfiable => Unsat,
    // and they agree for every assignment.
    virtual Result check(Lit lit) = 0;
    // What to print when saying which solver produced the answer.
    virtual std::string describe() const = 0;
};

// A session over `net`, which must outlive it.  Uses the linked library when
// `solver.command` names one and this build has it; otherwise re-serialises
// the network per question and runs the command, which is always available.
std::unique_ptr<Session> make_session(const BoolNet &net, const Solver &solver);

// Whether this build can make a linked session at all, for the usage text
// and for choosing a default.
bool have_linked_z3();

// The name that selects the linked library rather than an external binary.
inline const char *linked_z3_name() { return "libz3"; }

// CaDiCaL, linked: a CDCL SAT solver over a Tseitin encoding of the network, incremental through assumptions.  Several times faster
// than Z3 on these miters (which are pure Boolean, so an SMT engine buys nothing), and the default when this build has it.
bool have_linked_cadical();
inline const char *linked_cadical_name() { return "libcadical"; }

const char *to_string(Result r);

} // namespace lvs

#endif
