#include "solver.hpp"

#include "lvs/boolnet.hpp"

#include <array>
#include <cstdio>
#include <cstdlib>
#include <atomic>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <stdexcept>
#include <unistd.h>
#include <vector>

#ifdef _WIN32
// popen runs cmd.exe, which returns the exit code itself, discards output with
// NUL and says 9009 for a command it cannot find
#define LVS_DEVNULL "NUL"
#define LVS_NOT_FOUND(status) ((status) == 9009)
#else
#include <sys/wait.h>
#define LVS_DEVNULL "/dev/null"
#define LVS_NOT_FOUND(status) (WIFEXITED(status) && WEXITSTATUS(status) == 127)
#endif

#ifdef LVS_HAVE_CADICAL
#include <cadical.hpp>
#endif

#ifdef LVS_HAVE_Z3
#include <z3++.h>
#include <algorithm>
#endif

namespace lvs {

const char *to_string(Result r)
{
    switch (r) {
    case Result::Unsat:
        return "unsat";
    case Result::Sat:
        return "sat";
    default:
        return "unknown";
    }
}

Result run_solver(const Solver &solver, const std::string &text)
{
    namespace fs = std::filesystem;
    // pid plus a counter, not rand(): rand() is never seeded, so it yields the
    // same sequence every run and two concurrent runs in one temp directory
    // would collide on the first question, the second overwriting the first's
    // file while it was being read.  A counter cannot repeat within a process,
    // and the pid separates processes.
    static std::atomic<unsigned> seq{0};
    fs::path path = fs::temp_directory_path() /
                    ("lvs_miter_" + std::to_string(::getpid()) + "_" +
                     std::to_string(seq.fetch_add(1)) +
                     (solver.format == Format::Dimacs ? ".cnf" : ".smt2"));
    {
        std::ofstream out(path);
        if (!out)
            throw std::runtime_error("cannot write " + path.string());
        out << text;
    }

    std::string cmd = solver.command + " " + path.string() + " 2>" LVS_DEVNULL;
    std::string output;
    int status = -1;
    if (FILE *pipe = ::popen(cmd.c_str(), "r")) {
        std::array<char, 4096> buf;
        while (std::fgets(buf.data(), int(buf.size()), pipe))
            output += buf.data();
        status = ::pclose(pipe);
    }
    fs::remove(path);

    // A solver that is not installed says nothing, and saying nothing reads
    // as "could not decide" -- so a machine with no solver on it reports every
    // register unknown and looks exactly like a proof that did not go
    // through.  The shell says 127 when it cannot find the command; that is a
    // setup fault, not a result, and it is worth failing loudly over.
    if (status != -1 && LVS_NOT_FOUND(status))
        throw std::runtime_error("solver not found: '" + solver.command +
                                 "'. Install it, or pass --solver with one that exists"
                                 " (a build linked against libz3 defaults to --solver libz3).");

    // Both answer conventions in one pass: SAT solvers print "s SATISFIABLE",
    // SMT solvers print "sat".  Check unsat first -- "sat" is a substring of
    // "unsat", and of "UNSATISFIABLE" once lowercased.
    for (auto &c : output)
        c = char(::tolower(c));
    if (output.find("unsat") != std::string::npos)
        return Result::Unsat;
    if (output.find("sat") != std::string::npos)
        return Result::Sat;
    return Result::Unknown;
}

} // namespace lvs

// ---------------------------------------------------------------------------
// Sessions
// ---------------------------------------------------------------------------

namespace lvs {

namespace {

// The always-available session: state the whole problem again per question,
// hand it to a command, read the verdict off its stdout.  Correct, portable,
// and the only route to a solver we have not linked -- but it pays a process
// launch and a re-parse of the entire network for every register.
class CommandSession : public Session
{
  public:
    CommandSession(const BoolNet &net, Solver solver) : net_(net), solver_(std::move(solver)) {}

    Result check(Lit lit) override
    {
        std::ostringstream os;
        if (solver_.format == Format::Dimacs)
            write_dimacs(net_, lit, os);
        else
            write_smtlib2(net_, lit, os);
        return run_solver(solver_, os.str());
    }

    std::string describe() const override
    {
        return solver_.command + " (" + (solver_.format == Format::Dimacs ? "DIMACS" : "SMT-LIB2") +
               ", one process per question)";
    }

  private:
    const BoolNet &net_;
    Solver solver_;
};

} // namespace

#ifdef LVS_HAVE_CADICAL

namespace {

// The linked CaDiCaL session.  Node n is variable n+1 (variable 1 is the constant, held false); an AND node gets its three Tseitin clauses
// when a question first reaches it, and a question is one assumption.  Definitions are true whatever is asked, so clauses added for an
// earlier cone are reused and what the solver learned stays valid.
class CadicalSession : public Session
{
  public:
    explicit CadicalSession(const BoolNet &net) : net_(net)
    {
        solver_.add(-1);   // variable 1 is node 0, the constant: false
        solver_.add(0);
        done_.push_back(true);
    }

    Result check(Lit lit) override
    {
        encode_cone(node_of(lit));
        solver_.assume(sat_lit(lit));
        switch (solver_.solve()) {
        case 10: return Result::Sat;
        case 20: return Result::Unsat;
        default: return Result::Unknown;
        }
    }

    std::string describe() const override { return std::string("libcadical ") + CaDiCaL::Solver::version() + " (linked, incremental)"; }

  private:
    static int sat_lit(Lit l) { return is_inverted(l) ? -int(node_of(l) + 1) : int(node_of(l) + 1); }

    void encode_cone(uint32_t root)
    {
        const auto &ands = net_.ands();
        if (done_.size() < net_.node_count()) done_.resize(net_.node_count(), false);
        std::vector<uint32_t> stack{root};
        while (!stack.empty()) {
            uint32_t n = stack.back();
            if (done_[n]) { stack.pop_back(); continue; }
            auto it = ands.find(n);
            if (it == ands.end()) {            // an input: a free variable, no clauses
                done_[n] = true;
                stack.pop_back();
                continue;
            }
            uint32_t a = node_of(it->second.a), b = node_of(it->second.b);
            bool ready = true;
            if (!done_[a]) { stack.push_back(a); ready = false; }
            if (!done_[b]) { stack.push_back(b); ready = false; }
            if (!ready) continue;
            const int v = int(n + 1), x = sat_lit(it->second.a), y = sat_lit(it->second.b);
            solver_.add(-v); solver_.add(x); solver_.add(0);
            solver_.add(-v); solver_.add(y); solver_.add(0);
            solver_.add(v); solver_.add(-x); solver_.add(-y); solver_.add(0);
            done_[n] = true;
            stack.pop_back();
        }
    }

    const BoolNet &net_;
    CaDiCaL::Solver solver_;
    std::vector<bool> done_;
};

} // namespace

bool have_linked_cadical() { return true; }

#else

bool have_linked_cadical() { return false; }

#endif

#ifdef LVS_HAVE_Z3

namespace {

// The linked session.  Every AIG node becomes a Bool constant constrained to
// equal its definition, asserted once and never retracted -- a definition is
// true whatever is being asked.  A question is then one assumption, so the
// solver keeps everything it learned from the last one.
class Z3Session : public Session
{
  public:
    explicit Z3Session(const BoolNet &net) : net_(net), solver_(ctx_)
    {
        // node 0 is the constant, and literal 0 is FALSE
        expr_.push_back(ctx_.bool_val(false));
        done_.push_back(true);
    }

    Result check(Lit lit) override
    {
        encode_cone(node_of(lit));
        z3::expr_vector assumption(ctx_);
        assumption.push_back(lit_expr(lit));
        switch (solver_.check(assumption)) {
        case z3::unsat: return Result::Unsat;
        case z3::sat: return Result::Sat;
        default: return Result::Unknown;
        }
    }

    std::string describe() const override
    {
        unsigned major = 0, minor = 0, build = 0, rev = 0;
        Z3_get_version(&major, &minor, &build, &rev);
        return "libz3 " + std::to_string(major) + "." + std::to_string(minor) + "." +
               std::to_string(build) + " (linked, incremental)";
    }

  private:
    z3::expr lit_expr(Lit l) const
    {
        const z3::expr &e = expr_[node_of(l)];
        return is_inverted(l) ? !e : e;
    }

    // Only the nodes the question can reach.  A miter's cone is a small part of a SoC-sized network, and asserting a definition for every
    // node the network has ever grown (which is what this used to do) made the first question pay for all of them and every later one for the
    // growth in between.  A definition is true whatever is asked, so one encoded for an earlier cone is simply reused.  Iterative: a cone
    // can be deeper than the stack.
    void encode_cone(uint32_t root)
    {
        const auto &ands = net_.ands();
        if (expr_.size() < net_.node_count()) {
            expr_.resize(net_.node_count(), ctx_.bool_val(false));
            done_.resize(net_.node_count(), false);
        }
        std::vector<uint32_t> stack{root};
        while (!stack.empty()) {
            uint32_t n = stack.back();
            if (n == 0 || done_[n]) { stack.pop_back(); continue; }
            auto it = ands.find(n);
            if (it == ands.end()) {            // an input: a free variable
                expr_[n] = ctx_.bool_const(("n" + std::to_string(n)).c_str());
                done_[n] = true;
                stack.pop_back();
                continue;
            }
            uint32_t a = node_of(it->second.a), b = node_of(it->second.b);
            bool ready = true;
            if (a && !done_[a]) { stack.push_back(a); ready = false; }
            if (b && !done_[b]) { stack.push_back(b); ready = false; }
            if (!ready) continue;
            expr_[n] = ctx_.bool_const(("n" + std::to_string(n)).c_str());
            solver_.add(expr_[n] == (lit_expr(it->second.a) && lit_expr(it->second.b)));
            done_[n] = true;
            stack.pop_back();
        }
    }

    const BoolNet &net_;
    z3::context ctx_;
    z3::solver solver_;
    std::vector<z3::expr> expr_;   // node index -> its Bool constant
    std::vector<bool> done_;       // ...once its definition has been asserted
};

} // namespace

bool have_linked_z3() { return true; }

std::unique_ptr<Session> make_session(const BoolNet &net, const Solver &solver)
{
#ifdef LVS_HAVE_CADICAL
    if (solver.command == linked_cadical_name())
        return std::make_unique<CadicalSession>(net);
#endif
    if (solver.command == linked_z3_name())
        return std::make_unique<Z3Session>(net);
    return std::make_unique<CommandSession>(net, solver);
}

#else

bool have_linked_z3() { return false; }

std::unique_ptr<Session> make_session(const BoolNet &net, const Solver &solver)
{
#ifdef LVS_HAVE_CADICAL
    if (solver.command == linked_cadical_name())
        return std::make_unique<CadicalSession>(net);
#endif
    Solver s = solver;
    if (s.command == linked_z3_name())
        s.command = "z3";   // built without the library; the command still works
    return std::make_unique<CommandSession>(net, s);
}

#endif

} // namespace lvs
