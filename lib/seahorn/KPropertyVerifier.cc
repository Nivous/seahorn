#include "seahorn/KPropertyVerifier.hh"
#include "seahorn/HornifyModule.hh"
#include <string>

#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"

#define DOOMED_STATE_FUNCTION_NAME      "hyper.doomed.state"

namespace seahorn {
char KPropertyVerifier::ID = 0;

enum HyperProperties {
  PRE,
  POST
};

void KPropertyVerifier::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<HornifyModule>();
  AU.setPreservesAll();
}

static void print_vars(hyper_expr_map *k_vars) {
  for(hyper_expr_map::iterator it = k_vars->begin(); it != k_vars->end(); ++it)
  {
    errs() << "The new variables created for var: " << *(it->first) << "\n";
    for(std::map<int, Expr>::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2) {
      errs() << "i = " << it2->first << " : " << *(bind::name(it2->second)) << "\n";
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


void KPropertyVerifier::makeHyperVars(const ExprVector &vars, hyper_expr_map *k_vars) {
  int i;
  Expr name;
  Expr new_var;
  ExprVector sort;

  for (const Expr &var : vars) {
    k_vars->insert(std::pair<Expr, std::map<int, Expr>>(var, std::map<int, Expr>()));
    for (i = 0; i < hyper_k; i++) {
      name = variant::tag(var, "_thread_" + std::to_string(i));
      sort.push_back(bind::typeOf(var));
      new_var = bind::fdecl(name, sort);
      sort.clear();
      (*k_vars)[var].insert(std::pair<int, Expr>(i, new_var));
    }
  }
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
      sorts.push_back(bind::type(it2->second));

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

bool KPropertyVerifier::runOnModule(Module &M) {
  ScopedStats _st_("KPropertyVerifier");
  HornifyModule &hm = getAnalysis<HornifyModule>();

  hyper_expr_map k_vars;
  hyper_subset_expr_map doomed_rels;
  HornClauseDB &db = hm.getHornClauseDB();
  // Need to reset the DB after using it - add a function to reset.
  ExprFactory &m_efac = hm.getExprFactory();
  //EZ3 &z3 = hm.getZContext();

  const ExprVector &vars = db.getVars();
  const HornClauseDB::RuleVector &rules = db.getRules();
  const HornClauseDB::expr_set_type &rels = db.getRelations();

  makeHyperVars(vars, &k_vars); /* Get new vars */

  /* Insert doomed state function to symbol table */
  auto FC = M.getOrInsertFunction(DOOMED_STATE_FUNCTION_NAME, Type::getVoidTy(M.getContext()));
  auto *FN = dyn_cast<Function>(FC.getCallee());

  std::set<std::set<int>> k_subsets = generateAllSubsets(hyper_k);

  makeDoomedRels(k_vars, FN, k_subsets, m_efac, &doomed_rels);

  return true;
}

}
