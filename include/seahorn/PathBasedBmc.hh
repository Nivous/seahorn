#pragma once

#include "seahorn/Bmc.hh"
#include "seahorn/LegacyOperationalSemantics.hh"
#include "seahorn/LiveSymbols.hh"
#include "seahorn/config.h"

#include "boost/unordered_set.hpp"
//#include "boost/unordered_map.hpp"

#include <queue>

namespace llvm {
class TargetLibraryInfo;
}

#ifdef HAVE_CLAM
namespace clam {
class ClamPass;
class IntraClam;
} // namespace clam
#endif

/*
  Rather than building a monolithic precise encoding of the program
  and check its satisfiability, this BMC engine enumerates
  symbolically all paths using an abstraction of the precise encoding
  of the program. This enumeration continues until a path is
  satisfiable or no more paths exist.
 */
namespace seahorn {
class PathBasedBmcEngine : public BmcEngine {
public:
#ifdef HAVE_CLAM
  PathBasedBmcEngine(LegacyOperationalSemantics &sem, EZ3 &zctx,
                     clam::ClamPass *crab,
                     const llvm::TargetLibraryInfo &tli);
#else
  PathBasedBmcEngine(LegacyOperationalSemantics &sem, EZ3 &zctx,
                     const llvm::TargetLibraryInfo &tli);
#endif

  ~PathBasedBmcEngine();

  /// Enumerate paths until a path is satisfiable or there is no
  /// more paths.
  boost::tribool solve() override;

  /// Returns the BMC trace (if available)
  BmcTrace getTrace() override;

  // Return model if sat
  ZModel<EZ3> getModel() override;

  /// constructs the initial (precise) encoding
  /// but the encoding is not asserted in the solver.
  void encode(bool assert_formula) override;

  /// Dump unsat core if unsat (NOT implemented)
  void unsatCore(ExprVector &out) override;

  /// Output the initial (precise) encoding in SMT-LIB2 format
  raw_ostream &toSmtLib(raw_ostream &out) override;

  LegacyOperationalSemantics &sem() override {
    return static_cast<LegacyOperationalSemantics &>(BmcEngine::sem());
  }

private:
  // Incomplete flag: if a SMT query returned unknown
  bool m_incomplete;

  // Queue for unsolved path formulas
  std::queue<std::pair<unsigned, ExprVector>> m_unknown_path_formulas;

  // Count number of path
  unsigned m_num_paths;
  // used to solve a path formula
  ZSolver<EZ3> m_aux_smt_solver;
  const llvm::TargetLibraryInfo &m_tli;

  // Boolean literals that active the implicant: used to produce
  // blocking clauses for the Boolean abstraction.
  ExprVector m_active_bool_lits;
  // model of a path formula
  ZModel<EZ3> m_model;
  // live symbols
  LiveSymbols *m_ls;
#ifdef HAVE_CLAM
  // crab instance that includes invariants and heab abstraction information
  clam::ClamPass *m_crab_global;
  // crab instance to run only paths
  clam::IntraClam *m_crab_path;
#endif
  // Temporary sanity check: bookeeping of all generated blocking
  // clauses.
  boost::unordered_set<Expr> m_blocking_clauses;

  // Check feasibility of a path induced by model using SMT solver.
  // Return true (sat), false (unsat), or indeterminate (inconclusive).
  // If unsat then it produces a blocking clause.
  typedef DenseMap<const BasicBlock *, ExprVector> invariants_map_t;
  boost::tribool
  path_encoding_and_solve_with_smt(const BmcTrace &trace,
                                   const invariants_map_t &invariants,
                                   const invariants_map_t &path_constraints);

#ifdef HAVE_CLAM
  // Check feasibility of a path induced by trace using abstract
  // interpretation.
  // Return true (sat) or false (unsat). If unsat then it produces a
  // blocking clause.
  bool path_encoding_and_solve_with_ai(BmcTrace &trace,
                                       invariants_map_t &path_constraints);
  /// Out contains all invariants (per block) inferred by crab.
  void load_invariants(clam::ClamPass &crab, const LiveSymbols &ls,
                       DenseMap<const BasicBlock *, ExprVector> &out);

  /// Add the crab invariants in m_side after applying the symbolic store s.
  void assert_invariants(const invariants_map_t &invariants, SymStore &s);
#endif

  // Return false if a blocking clause has been generated twice.
  bool add_blocking_clauses();

  // For debugging
  void toSmtLib(const ExprVector &path, std::string prefix = "");
};
} // namespace seahorn
