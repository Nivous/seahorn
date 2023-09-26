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
    Function *m_hyper_post_gt;

    bool runOnModule(Module &M, SeaBuiltinsInfo& SBI);
    bool runOnFunction(Function &F);
    void splitHyperCallsToOwnBasicBlocks(Function &F);
  };
}

#endif /* PROMOTEHYPERCALLS_H */
