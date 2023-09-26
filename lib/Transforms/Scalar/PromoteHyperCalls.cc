#include "seahorn/Transforms/Scalar/PromoteHyperCalls.hh"
#include "seahorn/Support/Stats.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IRBuilder.h"

#include "boost/range.hpp"

#include "llvm/Support/raw_ostream.h"
#include <string>
using namespace llvm;

namespace seahorn {

bool PromoteHyperCalls::runOnModule(Module &M, SeaBuiltinsInfo& SBI) {
    ScopedStats _st("PromoteHyperCalls");
    LOG("phc", errs() << "Running promote-hyper-calls pass\n";);

    using SBIOp = SeaBuiltinsOp;

    m_hyper_pre_gt = SBI.mkSeaBuiltinFn(SBIOp::HYPER_PRE_GT, M);
    m_hyper_post_gt = SBI.mkSeaBuiltinFn(SBIOp::HYPER_POST_GT, M);

    for (auto &F : M) {
        runOnFunction(F);
        splitHyperCallsToOwnBasicBlocks(F);
    }
    errs() << "Module:\n";
    M.print(errs(), NULL);
    return true;
}

bool PromoteHyperCalls::runOnFunction(Function &F) {
    SmallVector<Instruction *, 16> toKill;

    Function *nfn;
    bool Changed = false;
    for (auto &I : instructions(F)) {
        if (!isa<CallInst>(&I))
            continue;

    // // -- look through pointer casts
    // Value *v = I.stripPointerCasts ();

    CallInst &CI = cast<CallInst>(I);
    const Function *fn = CI.getCalledFunction();

    // -- check if this is a call through a pointer cast
    if (!fn && CI.getCalledOperand())
      fn = dyn_cast<const Function>(CI.getCalledOperand()->stripPointerCasts());
    // -- expect functions we promote to not be defined in the module,
    // -- if they are defined, then do not promote and treat as regular
    // -- functions
    if (fn && !fn->empty())
      continue;

    if (fn && (fn->getName().equals("__hyper_pre_gt") ||
               fn->getName().equals("__hyper_post_gt"))) {
        auto arg0 = CI.getOperand(0);
       
        if (fn->getName().equals("__hyper_pre_gt"))
            nfn = m_hyper_pre_gt;
        else if(fn->getName().equals("__hyper_post_gt"))
            nfn = m_hyper_post_gt;
        else
          assert(0);

        // Generates code.
        IRBuilder<> Builder(F.getContext());
        Builder.SetInsertPoint(&I);
        Builder.CreateCall(nfn, (Value *)arg0);

        // Remove the original instruction.
        toKill.push_back(&I);
    }
  }

  for (auto *I : toKill)
    I->eraseFromParent();

  return Changed;
}

void PromoteHyperCalls::splitHyperCallsToOwnBasicBlocks(Function &F) {
    SmallVector<Instruction *, 16> toSplit;
    std::string name_before = "";
    std::string name_after = "";
    
    for (auto &I : instructions(F)) {
        if (!isa<CallInst>(&I))
            continue;

        // // -- look through pointer casts
        // Value *v = I.stripPointerCasts ();

        CallInst &CI = cast<CallInst>(I);
        const Function *fn = CI.getCalledFunction();

        // -- check if this is a call through a pointer cast
        if (!fn && CI.getCalledOperand())
            fn = dyn_cast<const Function>(CI.getCalledOperand()->stripPointerCasts());
            // -- expect functions we promote to not be defined in the module,
            // -- if they are defined, then do not promote and treat as regular
            // -- functions
        if (fn && !fn->empty())
            continue;

        if (fn && ((fn->getName().equals("hyper.post.gt")) ||
            (fn->getName().equals("hyper.pre.gt"))))
            toSplit.push_back(&I);
    }

    for (auto *I : toSplit) {
        if (I->getParent()->hasName()) {
            name_before = (std::string)I->getParent()->getName() + "_before";
            name_after = (std::string)I->getParent()->getName() + "_after";
        }

        if (&I->getParent()->front() != dyn_cast<Instruction>(I))
            I->getParent()->splitBasicBlock(I, name_before, true);
            // Split the commands before inst into another basic block.

        if (!I->getNextNode()->isTerminator())
            I->getParent()->splitBasicBlock(I->getNextNode(), name_after);
            // Split the commands after inst into another basic block.

        name_before = "";
        name_after = "";
    }
}
}
