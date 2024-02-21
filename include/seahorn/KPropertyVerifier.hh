#ifndef _K_PROPERTY_VERIFIER__HH__
#define _K_PROPERTY_VERIFIER__HH__

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"

#include <map>
#include <set>

#include "Expr/Expr.hh"
#include "Expr/Smt/Z3.hh"
#include "Expr/Smt/EZ3.hh"

#include "seahorn/HornifyModule.hh"
#include "seahorn/HornClauseDB.hh"

namespace seahorn
{
  using namespace llvm;
  using hyper_expr_map = std::map<Expr, std::map<int, Expr>>;
  using hyper_subset_expr_map = std::map<std::set<int>, Expr>;
  
  class KPropertyVerifier : public llvm::ModulePass
  {
    int hyper_k;
    bool m_interproc;

    void makeHyperVars(const ExprVector &vars, ExprFactory &m_efac, Module &M, hyper_expr_map &k_vars, ExprVector &all_k_vars);
    void makeDoomedRels(hyper_expr_map &vars, Function *fn,
                        std::set<std::set<int>> &k_subsets, ExprFactory &m_efac,
                        hyper_subset_expr_map *doomed_rels);
    void getHyperExprsFromFunction(Function &F, HornifyModule &hm, ExprFactory &m_efac, Module &M,
                                    hyper_expr_map &k_vars, std::set<std::set<int>> &k_subsets,
                                    std::map<const Function *, std::map<int, Expr>> &pc_rels,
                                    HornClauseDB::expr_set_type &pre_rules,
                                    ExprVector &bad_rules,
                                    std::map<std::set<int>, Expr> &valid_rules,
                                    std::map<const Function *, int> &max_pc);
    void getHyperExprsModule(Module &M, HornifyModule &hm, ExprFactory &m_efac,
                          hyper_expr_map &k_vars, std::set<std::set<int>> &k_subsets,
                          std::map<const Function *, std::map<int, Expr>> &pc_rels,
                          HornClauseDB::expr_set_type &pre_rules,
                          ExprVector &bad_rules,
                          std::map<std::set<int>, Expr> &valid_rules,
                          std::map<const Function *, int> &max_pc);
    void getPcRels(const HornClauseDB::expr_set_type &orig_rels,
                    std::map<const Function *, std::map<int, Expr>> &new_rels,
                    ExprFactory &m_efac, Module &M, hyper_expr_map &k_rels,
                    std::map<const Function *, Expr>& pc_combined_rel);
    void getValidExprs(std::map<std::set<int>, ExprVector> &obvPoint,
                        std::set<std::set<int>> &k_subsets,
                        std::map<std::set<int>, Expr> &valid_rules);
    void getBadExprs(std::map<std::set<int>, ExprVector> &obvPoint,
                      ExprVector &bad_rules,
                      Expr post);
    void getObservationPointExprs(std::map<std::set<int>, ExprVector> &obvPoint,
                                  ExprVector &args, std::map<int, Expr> &steps,
                                  std::set<std::set<int>> &k_subsets,
                                  hyper_expr_map &k_vars);
    void getTraceInfo(Module &M, std::map<const Function *, std::map<std::pair<int, int>, ExprVector[3]>> &trace_info,
                      const HornClauseDB::expr_set_type &orig_rels, ExprFactory &m_efac,
                      const HornClauseDB::RuleVector &rules);
    void getTraceRulesFromInfo(std::map<const Function *, std::map<std::pair<int, int>, ExprVector[3]>> &trace_info,
                                hyper_expr_map &k_vars,
                                std::map<const Function *, std::map<std::pair<int, int>, std::map<int, Expr>>> &trace_rules);
    void getTraceRules(ExprVector &all_k_vars, hyper_expr_map &k_vars, hyper_expr_map &k_rels,
                        std::set<std::set<int>> &k_subsets,
                        std::map<const Function *, std::map<std::pair<int, int>, ExprVector[3]>>& trace_info,
                        hyper_subset_expr_map &doomed_rels,
                        std::map<const Function *, std::map<std::pair<int, int>, std::map<int, Expr>>> &trace_rules,
                        std::map<const Function *, int> &max_pc,
                        std::map<std::pair<int, int>, std::map<std::set<int>, Expr>> &final_trace_rules);
  public:
    static char ID;
    KPropertyVerifier (int hyper_k, bool interproc = false) : llvm::ModulePass (ID), hyper_k(hyper_k), m_interproc(interproc) {}
    virtual ~KPropertyVerifier() = default;
    virtual StringRef getPassName() const override {return "KPropertyVerifier";}
    
    virtual bool runOnModule(Module &M) override;
    virtual void getAnalysisUsage(AnalysisUsage &AU) const override;
  };
}

#endif /* _K_PROPERTY_VERIFIER__HH__ */
