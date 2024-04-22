#include "seahorn/Transforms/Scalar/PromoteHyperCalls.hh"
#include "seahorn/Support/Stats.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IRBuilder.h"

#include "boost/range.hpp"

#include "llvm/IR/Instructions.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <string>
using namespace llvm;

namespace seahorn {

static void changeCall(Instruction *I, Function *nfn) {
    CallInst *c = dyn_cast<CallInst>(I);
    c->setCalledFunction(nfn);
}

bool PromoteHyperCalls::runOnModule(Module &M, SeaBuiltinsInfo& SBI) {
    ScopedStats _st("PromoteHyperCalls");
    LOG("phc", errs() << "Running promote-hyper-calls pass\n";);

    using SBIOp = SeaBuiltinsOp;

    m_hyper_pre_gt = SBI.mkSeaBuiltinFn(SBIOp::HYPER_PRE_GT, M);
    m_hyper_pre_geq = SBI.mkSeaBuiltinFn(SBIOp::HYPER_PRE_GEQ, M);
    m_hyper_pre_eq = SBI.mkSeaBuiltinFn(SBIOp::HYPER_PRE_EQ, M);
    m_hyper_pre_neq = SBI.mkSeaBuiltinFn(SBIOp::HYPER_PRE_NEQ, M);
    m_hyper_pre_lt = SBI.mkSeaBuiltinFn(SBIOp::HYPER_PRE_LT, M);
    m_hyper_pre_leq = SBI.mkSeaBuiltinFn(SBIOp::HYPER_PRE_LEQ, M);
    m_hyper_post_gt = SBI.mkSeaBuiltinFn(SBIOp::HYPER_POST_GT, M);
    m_hyper_post_geq = SBI.mkSeaBuiltinFn(SBIOp::HYPER_POST_GEQ, M);
    m_hyper_post_eq = SBI.mkSeaBuiltinFn(SBIOp::HYPER_POST_EQ, M);
    m_hyper_post_neq = SBI.mkSeaBuiltinFn(SBIOp::HYPER_POST_NEQ, M);
    m_hyper_post_lt = SBI.mkSeaBuiltinFn(SBIOp::HYPER_POST_LT, M);
    m_hyper_post_leq = SBI.mkSeaBuiltinFn(SBIOp::HYPER_POST_LEQ, M);
    m_hyper_non_det = SBI.mkSeaBuiltinFn(SBIOp::HYPER_NON_DET, M);
    m_hyper_assume = SBI.mkSeaBuiltinFn(SBIOp::HYPER_ASSUME, M);

    for (auto &F : M) {
        runOnFunction(F);
        splitHyperCallsToOwnBasicBlocks(F);
    }

    return true;
}

bool PromoteHyperCalls::runOnFunction(Function &F) {
    SmallVector<Instruction *, 32> toKill;

    Function *nfn;
    bool Changed = false;
    for (auto &I : instructions(F)) {
        bool send_args = true;
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

    if (fn && fn->getName().startswith("__hyper")) {
        auto arg0 = CI.getOperand(0);
       
        if (fn->getName().equals("__hyper_pre_gt"))
            nfn = m_hyper_pre_gt;
        else if (fn->getName().equals("__hyper_pre_geq"))
            nfn = m_hyper_pre_geq;
        else if (fn->getName().equals("__hyper_pre_eq"))
            nfn = m_hyper_pre_eq;
        else if (fn->getName().equals("__hyper_pre_neq"))
            nfn = m_hyper_pre_neq;
        else if (fn->getName().equals("__hyper_pre_lt"))
            nfn = m_hyper_pre_lt;
        else if (fn->getName().equals("__hyper_pre_leq"))
            nfn = m_hyper_pre_leq;
        else if(fn->getName().equals("__hyper_post_gt"))
            nfn = m_hyper_post_gt;
        else if (fn->getName().equals("__hyper_post_geq"))
            nfn = m_hyper_post_geq;
        else if (fn->getName().equals("__hyper_post_eq"))
            nfn = m_hyper_post_eq;
        else if (fn->getName().equals("__hyper_post_neq"))
            nfn = m_hyper_post_neq;
        else if (fn->getName().equals("__hyper_post_lt"))
            nfn = m_hyper_post_lt;
        else if (fn->getName().equals("__hyper_post_leq"))
            nfn = m_hyper_post_leq;
        else if (fn->getName().equals("__hyper_non_det")) {
            nfn = m_hyper_non_det;
            send_args = false;
        } else if (fn->getName().equals("__hyper_assume"))
            nfn = m_hyper_assume;
        else
          assert(0 && "Unknown hyper call");

        // Generates code.
        IRBuilder<> Builder(F.getContext());
        Builder.SetInsertPoint(&I);
        if (send_args)
            Builder.CreateCall(nfn, (Value *)arg0);
        else
            changeCall(&I, nfn);

        // Remove the original instruction.
        if (send_args)
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

        if (fn && (fn->getName().startswith("hyper.pre") ||
            fn->getName().startswith("hyper.post") ||
            fn->getName().equals("hyper.assume")))
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
