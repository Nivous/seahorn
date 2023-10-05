#include "seahorn/KPropertyVerifier.hh"
#include "seahorn/UfoOpSem.hh"
#include <string>

#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IRBuilder.h"


#define DOOMED_STATE_FUNCTION_NAME      "hyper.doomed.state"

namespace seahorn {
char KPropertyVerifier::ID = 0;

void KPropertyVerifier::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<HornifyModule>();
  AU.setPreservesAll();
}

static void print_vars(hyper_expr_map *k_vars) {
  for(hyper_expr_map::iterator it = k_vars->begin(); it != k_vars->end(); ++it)
  {
    errs() << "The new variables created for var: " << *(it->first) << "\n";
    for(std::map<int, Expr>::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2) {
      errs() << "i = " << it2->first << " : " << *(it2->second) << "\n";
    }
  }
}

static void print_rels(hyper_subset_expr_map *doomed_rels) {
  for(hyper_subset_expr_map::iterator it = doomed_rels->begin(); it != doomed_rels->end(); ++it)
  {
    Expr decl = it->second;
    errs() << "(declare-rel " << *bind::fname(decl) << " (";
    for (unsigned i = 0; i < bind::domainSz(decl); i++) {
      Expr ty = bind::domainTy(decl, i);
      if (isOpX<BOOL_TY>(ty))
        errs() << "Bool ";
      else if (isOpX<REAL_TY>(ty))
        errs() << "Real ";
      else if (isOpX<INT_TY>(ty))
        errs() << "Int ";
      else if (isOpX<ARRAY_TY>(ty)) {
        errs() << "(Array ";
        if (isOpX<INT_TY>(sort::arrayIndexTy(ty)))
          errs() << "Int ";
        else if (isOpX<BVSORT>(sort::arrayIndexTy(ty))) {
          errs() << "(_ BitVec " << bv::width(sort::arrayIndexTy(ty)) << ") ";
        } else {
          errs() << "UfoUnknownSort ";
          llvm::errs() << "u1: " << *sort::arrayIndexTy(ty) << "\n";
        }
        if (isOpX<INT_TY>(sort::arrayValTy(ty)))
          errs() << "Int";
        else if (isOpX<BVSORT>(sort::arrayValTy(ty))) {
          errs() << "(_ BitVec " << bv::width(sort::arrayValTy(ty)) << ") ";
        } else {
          errs() << "UfoUnknownSort";
          llvm::errs() << "u2: " << *sort::arrayValTy(ty) << "\n";
        }
        errs() << ") ";
      } else if (isOpX<BVSORT>(ty)) {
        errs() << "(_ BitVec " << bv::width(ty) << ") ";
      } else {
        errs() << "UfoUnknownSort ";
        llvm::errs() << "u3: " << *ty << "\n";
      }
    }
    errs() << "))\n";
  }
}

static void print_hyper_rules(DenseMap<const BasicBlock *, Expr> &exprs) {
  errs() << "Rules are:\n";

  for (DenseMapIterator<const BasicBlock *, Expr> it = exprs.begin(); it != exprs.end(); it++)
    errs() << "rule: " << *(it->second) << "\n";

  errs() << "End of function\n";
}

static void generateSubsets(int n, std::set<int> &currentSubset, std::set<std::set<int>> &allSubsets, int index) {
    if (index == n + 1) {
      if (!currentSubset.empty())
        allSubsets.insert(currentSubset);
      return;
    }

    // Exclude the current element and generate subsets
    generateSubsets(n, currentSubset, allSubsets, index + 1);

    // Include the current element and generate subsets
    currentSubset.insert(index);
    generateSubsets(n, currentSubset, allSubsets, index + 1);

    // Backtrack
    currentSubset.erase(index);
}

static std::set<std::set<int>> generateAllSubsets(int n) {
    std::set<std::set<int>> allSubsets;
    std::set<int> currentSubset;
    generateSubsets(n, currentSubset, allSubsets, 1);
    return allSubsets;
}

void KPropertyVerifier::makeHyperVars(const ExprVector &vars, ExprFactory &m_efac, Module &M, hyper_expr_map &k_vars) {
  int i;
  Expr new_var;

  for (const Expr &var : vars) {
    k_vars.insert(std::pair<Expr, std::map<int, Expr>>(var, std::map<int, Expr>()));

    for (i = 0; i < hyper_k; i++) {
      Expr fdecl = bind::fname(var);
      Expr fname = bind::fname(fdecl);
      fname = variant::tag(fname, "_thread_" + std::to_string(i));
      Expr new_var = bind::reapp(var, bind::rename(fdecl, fname));
      k_vars[var].insert(std::pair<int, Expr>(i, new_var));
    }
  }

  print_vars(&k_vars);
}

void KPropertyVerifier::makeDoomedRels(hyper_expr_map &vars, Function *fn,
                                        std::set<std::set<int>> &k_subsets, ExprFactory &m_efac,
                                        hyper_subset_expr_map *doomed_rels) {
  ExprVector sorts;
  Expr orig_name = mkTerm<const Function *>(fn, m_efac);
  Expr name;
  std::string suffix;

  for(hyper_expr_map::iterator it = vars.begin(); it != vars.end(); ++it)
    for(std::map<int, Expr>::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2)
      sorts.push_back(bind::typeOf(it2->second));

  sorts.push_back(mk<BOOL_TY>(m_efac));

  for (std::set<int> subset : k_subsets) {
    suffix = "_subset";
    for (int i: subset)
      suffix += "_" + std::to_string(i);

    Expr name = variant::tag(orig_name, suffix);
    (*doomed_rels)[subset] = bind::fdecl(name, sorts);
  }
  print_rels(doomed_rels);
}

void KPropertyVerifier::getHyperExprsFromFunction(Function &F, HornifyModule &hm, ExprFactory &m_efac, Module &M,
                                                  DenseMap<const BasicBlock *, Expr> &pre_exprs,
                                                  DenseMap<const BasicBlock *, Expr> &post_exprs,
                                                  hyper_expr_map &k_vars) {
  const LiveSymbols &ls = hm.getLiveSybols(F);
  UfoOpSem m_sem(m_efac, hm, M.getDataLayout());

  // globally live
  ExprSet glive;

  for (auto &BB : F) {
    auto &live = ls.live(&BB);
    glive.insert(live.begin(), live.end());
  }

  ExprSet allVars;
  ExprVector args;
  SymStore s(m_efac);

  for (const Expr &v : glive)
    args.push_back(s.read(v));
  allVars.insert(args.begin(), args.end());

  for (auto &BB : F) {
    const BasicBlock *bb = &BB;
    allVars.clear();
    s.reset();
    args.clear();

    for (const Expr &v : glive)
      args.push_back(s.read(v));
    allVars.insert(args.begin(), args.end());
    assert(std::all_of(allVars.begin(), allVars.end(), bind::IsConst()));

    // Analyze block
    ExprVector side;
    m_sem.execHyper(s, BB, side, hyper_k, k_vars);

    const Instruction &inst = bb->front();
    if (!isa<CallInst>(&inst))
      continue;

    const CallInst &CI = cast<CallInst>(inst);
    const Function *fn = CI.getCalledFunction();

    if (!fn)
      continue;

    if (fn->getName().startswith("hyper.pre."))
      pre_exprs[bb] = side[0];

    if (fn->getName().startswith("hyper.post."))
      post_exprs[bb] = side[0];
  }
}

void KPropertyVerifier::getHyperExprsModule(Module &M, HornifyModule &hm, ExprFactory &m_efac,
                                            DenseMap<const BasicBlock *, Expr> &pre_exprs,
                                            DenseMap<const BasicBlock *, Expr> &post_exprs,
                                            hyper_expr_map &k_vars) {
  for (Function &F : M) {
    if (!F.empty())
      getHyperExprsFromFunction(F, hm, m_efac, M, pre_exprs, post_exprs, k_vars);
  }
}

bool KPropertyVerifier::runOnModule(Module &M) {
  ScopedStats _st_("KPropertyVerifier");
  HornifyModule &hm = getAnalysis<HornifyModule>();
  HornClauseDB &db = hm.getHornClauseDB();
  // Need to reset the DB after using it - add a function to reset.
  ExprFactory &m_efac = hm.getExprFactory();
  //EZ3 &z3 = hm.getZContext();

    hyper_expr_map k_vars;
    hyper_subset_expr_map doomed_rels;
    DenseMap<const BasicBlock *, Expr> pre_exprs;
    DenseMap<const BasicBlock *, Expr> post_exprs;

  if (hm.getStepSize() != hm_detail::FLAT_SMALL_STEP) {
    errs() << "Currently hyper properties supports only flat small step [step = " << hm.getStepSize() << " ].\n";
    return true;
  }

  const ExprVector &vars = db.getVars();
  const HornClauseDB::RuleVector &rules = db.getRules();
  const HornClauseDB::expr_set_type &rels = db.getRelations();

  makeHyperVars(vars, m_efac, M, k_vars); /* Get new vars */

  /* Insert doomed state function to symbol table */
  auto FC = M.getOrInsertFunction(DOOMED_STATE_FUNCTION_NAME, Type::getVoidTy(M.getContext()));
  auto *FN = dyn_cast<Function>(FC.getCallee());

  std::set<std::set<int>> k_subsets = generateAllSubsets(hyper_k);

  makeDoomedRels(k_vars, FN, k_subsets, m_efac, &doomed_rels);

  getHyperExprsModule(M, hm, m_efac, pre_exprs, post_exprs, k_vars);

  print_hyper_rules(pre_exprs);
  print_hyper_rules(post_exprs);

  return true;
}

}
