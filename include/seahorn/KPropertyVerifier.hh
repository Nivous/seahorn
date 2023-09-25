#ifndef _K_PROPERTY_VERIFIER__HH__
#define _K_PROPERTY_VERIFIER__HH__

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"

namespace seahorn
{
  using namespace llvm;
  
  
  class KPropertyVerifier : public llvm::ModulePass
  {
    int hyper_k;
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
