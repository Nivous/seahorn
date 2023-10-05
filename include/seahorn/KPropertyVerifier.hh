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

    void makeHyperVars(const ExprVector &vars, ExprFactory &m_efac, Module &M, hyper_expr_map &k_vars);
    void makeDoomedRels(hyper_expr_map &vars, Function *fn,
                        std::set<std::set<int>> &k_subsets, ExprFactory &m_efac,
                        hyper_subset_expr_map *doomed_rels);
    void getHyperExprs(enum HyperProperties type, Module &M, ExprFactory &m_efac, const ExprVector &orig_vars);
    void handleHyperGT(std::map<Expr, const BasicBlock *> *exprs, Expr var,  const BasicBlock *bb);
    void getHyperExprsFromFunction(Function &F, HornifyModule &hm, ExprFactory &m_efac, Module &M,
                                                  DenseMap<const BasicBlock *, Expr> &pre_exprs,
                                                  DenseMap<const BasicBlock *, Expr> &post_exprs,
                                                  hyper_expr_map &k_vars);
    void getHyperExprsModule(Module &M, HornifyModule &hm, ExprFactory &m_efac,
                                            DenseMap<const BasicBlock *, Expr> &pre_exprs,
                                            DenseMap<const BasicBlock *, Expr> &post_exprs,
                                            hyper_expr_map &k_vars);
  public:
    static char ID;
    KPropertyVerifier (int hyper_k) : llvm::ModulePass (ID), hyper_k(hyper_k) {}
    virtual ~KPropertyVerifier() = default;
    virtual StringRef getPassName() const override {return "KPropertyVerifier";}
    
    virtual bool runOnModule(Module &M) override;
    virtual void getAnalysisUsage(AnalysisUsage &AU) const override;
  };
}

#endif /* _K_PROPERTY_VERIFIER__HH__ */
