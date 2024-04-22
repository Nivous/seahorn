#ifndef PROMOTEHYPERCALLS_H
#define PROMOTEHYPERCALLS_H

/**
 * Promote Hyper calls and create a basic block dedicated for them
 */

#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

#include "seahorn/Analysis/SeaBuiltinsInfo.hh"

namespace seahorn
{
  using namespace llvm;
  
  struct PromoteHyperCalls {

    Function *m_hyper_pre_gt;
    Function *m_hyper_pre_geq;
    Function *m_hyper_pre_eq;
    Function *m_hyper_pre_neq;
    Function *m_hyper_pre_lt;
    Function *m_hyper_pre_leq;
    Function *m_hyper_post_gt;
    Function *m_hyper_post_geq;
    Function *m_hyper_post_eq;
    Function *m_hyper_post_neq;
    Function *m_hyper_post_lt;
    Function *m_hyper_post_leq;
    Function *m_hyper_non_det;

    bool runOnModule(Module &M, SeaBuiltinsInfo& SBI);
    bool runOnFunction(Function &F);
    void splitHyperCallsToOwnBasicBlocks(Function &F);
  };
}

#endif /* PROMOTEHYPERCALLS_H */
