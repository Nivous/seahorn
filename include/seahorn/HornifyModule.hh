#ifndef __HORNIFY_MODULE_HH_
#define __HORNIFY_MODULE_HH_

#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/LegacyOperationalSemantics.hh"

#include "boost/smart_ptr/scoped_ptr.hpp"

#include "seahorn/LiveSymbols.hh"

#include "seahorn/Analysis/CanFail.hh"
#include "seahorn/Analysis/CutPointGraph.hh"
#include "seahorn/Analysis/SeaBuiltinsInfo.hh"
#include "seahorn/HornClauseDB.hh"

#include "seahorn/InterMemPreProc.hh"

namespace hm_detail {
enum Step {
  SMALL_STEP,
  LARGE_STEP,
  CLP_SMALL_STEP,
  CLP_FLAT_SMALL_STEP,
  FLAT_SMALL_STEP,
  FLAT_LARGE_STEP,
  INC_SMALL_STEP
};
}

namespace seahorn {
using namespace expr;
using namespace llvm;
using namespace seahorn;

class HornifyModule : public llvm::ModulePass {
  typedef llvm::DenseMap<const Function *, LiveSymbols> LiveSymbolsMap;
  typedef llvm::DenseMap<const BasicBlock *, Expr> PredDeclMap;

protected:
  ExprFactory m_efac;
  EZ3 m_zctx;
  HornClauseDB m_db;

  const DataLayout *m_td;
  const CanFail *m_canFail;
  std::unique_ptr<LegacyOperationalSemantics> m_sem;

  LiveSymbolsMap m_ls;
  PredDeclMap m_bbPreds;

  // TODO: make private?
  std::shared_ptr<InterMemPreProc> m_imPreProc = nullptr;
  ShadowMem *m_shadowMem = nullptr;

  enum hm_detail::Step step_size;
  int hyper_k;
  bool m_interproc;

public:
  static char ID;
  HornifyModule(int hyper_k);
  virtual ~HornifyModule() {}
  ExprFactory &getExprFactory() { return m_efac; }
  EZ3 &getZContext() { return m_zctx; }
  HornClauseDB &getHornClauseDB() { return m_db; }
  virtual bool runOnModule(Module &M) override;
  virtual bool runOnFunction(Function &F);
  virtual void getAnalysisUsage(AnalysisUsage &AU) const override;
  virtual StringRef getPassName() const override { return "HornifyModule"; }

  /// --- live symbols for a function
  const LiveSymbols &getLiveSybols(const Function &F) const;
  /// -- live symbols for a basic block
  const ExprVector &live(const BasicBlock &bb) const {
    return getLiveSybols(*bb.getParent()).live(&bb);
  }
  /// --- live symbols for a basic block
  const ExprVector &live(const BasicBlock *bb) const {
    assert(bb != NULL);
    return live(*bb);
  }
  bool hasBbPredicate(const BasicBlock &BB) const {
    return m_bbPreds.count(&BB);
  }
  /// -- predicate declaration for the given basic block
  const Expr bbPredicate(const BasicBlock &bb);
  /// --- BasicBlock corresponding to the predicate
  const BasicBlock &predicateBb(Expr pred) const;
  /// --- Checks whether the expression is a BasicBlock predicate
  bool isBbPredicate(Expr pred) const;
  /// -- summary predicate for a function
  const Expr summaryPredicate(const Function &F) {
    return m_sem->hasFunctionInfo(F) ? m_sem->getFunctionInfo(F).sumPred
                                     : Expr(0);
  }
  /// -- symbolic execution engine
  LegacyOperationalSemantics &symExec() { return *m_sem; }

  CutPointGraph &getCpg(Function &F) { return getAnalysis<CutPointGraph>(F); }
  InterMemPreProc &getInterMemPP() {
    assert(m_imPreProc);
    return *m_imPreProc;
  }

  ShadowMem &getShadowMem() {
    assert(m_shadowMem);
    return *m_shadowMem;
  }

  SeaBuiltinsInfo &getSBI() {
    return getAnalysis<SeaBuiltinsInfoWrapperPass>().getSBI();
  }

  enum hm_detail::Step getStepSize() {return step_size;}

  int getHyperK() {return hyper_k;}

  bool getInterProc() {return m_interproc;}
};
} // namespace seahorn

#endif
