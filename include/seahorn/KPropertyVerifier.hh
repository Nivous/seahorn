#ifndef _K_PROPERTY_VERIFIER__HH__
#define _K_PROPERTY_VERIFIER__HH__

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"

#include <map>
#include <set>

#include "Expr/Expr.hh"
#include "Expr/Smt/Z3.hh"
#include "Expr/Smt/EZ3.hh"

#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornClauseDB.hh"

namespace seahorn
{
  using namespace llvm;
  using hyper_expr_map = std::map<Expr, std::map<int, Expr>>;

  struct functionResultAggregator {
    HornClauseDB::RuleVector rules;
    HornClauseDB::expr_set_type relations;
  };
  
  class KPropertyVerifier : public llvm::ModulePass
  {
    int hyper_k;
    bool m_interproc;

    void makeHyperVars(const ExprVector &vars, ExprFactory &m_efac,
                        hyper_expr_map &k_vars, ExprVector &all_k_vars);
    void makePcVars(ExprVector &pc_vars, const Function *F, ExprFactory &m_efac);
    void makeDoomedRels(hyper_expr_map &vars, Function *fn,
                        std::set<std::set<int>> &k_subsets, ExprFactory &m_efac,
                        std::map<std::set<int>, Expr> *doomed_rels);
    void getHyperExprsFromFunction(const Function *F, HornifyModule &hm, ExprFactory &m_efac, Module &M,
                                    hyper_expr_map &k_vars, std::set<std::set<int>> &k_subsets,
                                    std::map<int, Expr> &pc_rels,
                                    ExprVector &pre_rules,
                                    int *max_pc, std::set<int> &obv_point_pc,
                                    std::map<int, Expr> &obv_point_to_post);
    void getPcRels(const Function *F, const HornClauseDB::expr_set_type &orig_rels,
                    std::map<int, Expr> &new_rels, ExprFactory &m_efac, hyper_expr_map &k_rels,
                    Expr *pc_combined_rel);
    void getValidExprs(std::map<int, std::map<int, Expr>> &obvPoint,
                        std::set<std::set<int>> &k_subsets,
                        std::map<int, std::map<std::set<int>, Expr>> &valid_rules);
    void getBadExprs(std::map<int, std::map<int, Expr>> &obvPoint,
                      std::map<int, Expr> &bad_rules,
                      std::map<int, Expr> &obv_point_to_post);
    void getObservationPointExprs(std::map<int, std::map<int, Expr>> &obvPoint,
                                  std::set<std::set<int>> &k_subsets, ExprVector &pc_vars,
                                  std::set<int> &obv_point_pc, std::map<int, Expr> &pc_expr_map);
    void getTraceInfo(const Function *F, std::map<std::pair<int, int>, ExprVector[3]> &trace_info,
                      const HornClauseDB::expr_set_type &orig_rels, ExprFactory &m_efac,
                      const HornClauseDB::RuleVector &rules, std::map<int, Expr> &pc_expr_map,
                      std::map<int, std::vector<int>> &src_dst_map);
    void getTraceRulesFromInfo(const Function *F,
                                std::map<std::pair<int, int>, ExprVector[3]> &trace_info, hyper_expr_map &k_vars,
                                std::map<std::pair<int, int>, std::map<int, Expr>> &trace_rules);
    void getTraceRules(const Function *F, ExprVector &all_k_vars, hyper_expr_map &k_vars,
                        Expr pc_combined_rel, std::map<int, Expr> &pc_rels,
                        std::set<std::set<int>> &k_subsets,
                        std::vector<std::vector<int>> &k_ary_pc_vectors,
                        std::map<std::pair<int, int>, ExprVector[3]>& trace_info,
                        std::map<std::set<int>, Expr> &doomed_rels,
                        std::map<std::pair<int, int>, std::map<int, Expr>> &trace_rules,
                        std::map<std::vector<int>, std::map<std::set<int>, HornClauseDB::RuleVector>> &final_trace_rules,
                        std::map<int, Expr> &pc_expr_map, std::map<int, std::vector<int>> &src_dst_map);
    void getDoomedPreExpr(ExprVector &pre_rules,
                          std::map<std::set<int>, Expr> &doomed_rels,
                          ExprVector &all_k_vars, std::set<std::set<int>> &k_subsets,
                          HornClauseDB::RuleVector &doomed_pre_expr, Expr bottom_rel_expr,
                          ExprVector &pc_vars);
    void getValidRules(std::map<int, std::map<std::set<int>, Expr>> &valid_rules,
                        ExprVector &all_k_vars,
                        std::map<std::set<int>, Expr> &doomed_rels,
                        std::set<std::set<int>> &k_subsets,
                        HornClauseDB::RuleVector &valid_horn_rules,
                        ExprVector &pc_vars);
    void getBadRules(std::map<int, Expr> &bad_rules, ExprVector &all_k_vars,
                      std::map<std::set<int>, Expr> &doomed_rels,
                      std::set<std::set<int>> &k_subsets,
                      HornClauseDB::RuleVector &bad_horn_rules,
                      ExprVector &pc_vars);
    void runOnFunction(const Function *F, ExprFactory &m_efac, const ExprVector &vars,
                                      const HornClauseDB::RuleVector &rules, const HornClauseDB::expr_set_type &rels,
                                      std::set<std::set<int>> &k_subsets, HornifyModule &hm, Module &M,
                                      Expr bottom_rel_expr, struct functionResultAggregator *out,
                                      ExprVector &all_k_vars, hyper_expr_map &k_vars);
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
