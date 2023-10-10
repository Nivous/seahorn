#include "seahorn/KPropertyVerifier.hh"
#include "seahorn/UfoOpSem.hh"
#include "seahorn/Support/ExprSeahorn.hh"
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

static void print_doomed_rels(hyper_subset_expr_map *doomed_rels) {
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

static void print_hyper_rules(DenseMap<const BasicBlock *, Expr> &exprs, std::string print) {
  errs() << print << " Rules are:\n";

  for (DenseMapIterator<const BasicBlock *, Expr> it = exprs.begin(); it != exprs.end(); it++)
    errs() << "rule: " << *(it->second) << "\n";
}

static void print_pc_rels(std::map<const Function *, std::map<int, Expr>> &new_rels) {
  for(std::map<const Function *, std::map<int, Expr>>::iterator it = new_rels.begin(); it != new_rels.end(); ++it)
  {
    errs() << "The new pc rels for function: " << *(variant::mainVariant(bind::fname((it->second)[0]))) << "\n";
    for(std::map<int, Expr>::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2) {
      errs() << "i = " << it2->first << " : " << *(it2->second) << "\n";
    }
  }
}

static void print_obv_exprs(std::map<std::set<int>, ExprVector> &obvPoint) {
  for (std::map<std::set<int>, ExprVector>::iterator it = obvPoint.begin(); it != obvPoint.end(); it++) {
    errs() << "Observation point expressions for subset: ";
    for (int i: it->first) {
      errs() << i << "_";
    }
    errs() << "\n";

    for (Expr e : it->second)
      errs() << *e << "\n";
  }
}

static void print_valid_rules(std::map<std::set<int>, Expr> &valid_rules) {
  for (std::map<std::set<int>, Expr>::iterator it = valid_rules.begin(); it != valid_rules.end(); it++) {
    errs() << "Valid expressions for subset: ";
    for (int i: it->first) {
      errs() << i << "_";
    }
    errs() << "\n" << *(it->second) << "\n";
  }
}

static void print_bad_rules(ExprVector &bad_rules) {
  errs() << "The bad rules are:\n";
  for (Expr e : bad_rules)
    errs() << *e << "\n";
}

static void print_pre_rules(HornClauseDB::expr_set_type &pre_rules) {
  errs() << "Pre rules are:\n";
  for (Expr e : pre_rules)
    errs() << *e << "\n";
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
    generateSubsets(n - 1, currentSubset, allSubsets, 0);
    return allSubsets;
}

static Expr getFunctionRelFromDB(const HornClauseDB::expr_set_type &orig_rels, Expr name) {
  std::stringstream _st;
  _st << *name;
  std::string name_str = _st.str();

  for (Expr rel : orig_rels) {
    std::stringstream st;
    st << *(bind::fname(rel));
    if (st.str() == name_str)
      return rel;
  }

  return Expr(0);
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
  Expr pc = bind::intConst(mkTerm<std::string>("flat.pc", m_efac));

  sorts.push_back(bind::typeOf(pc));
  sorts.push_back(bind::typeOf(pc));

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
  print_doomed_rels(doomed_rels);
}

void KPropertyVerifier::getObservationPointExprs(std::map<std::set<int>, ExprVector> &obvPoint,
                                                  ExprVector &args, std::map<int, Expr> &steps,
                                                  std::set<std::set<int>> &k_subsets,
                                                  hyper_expr_map &k_vars) {
  Expr pc = args[0];
  args.erase(args.begin());
  for (std::set<int> subset : k_subsets) {
    ExprVector side;
    ExprVector _args;

    for (int i : subset) {
      _args.push_back(pc);
      Expr step = steps[i];
      for (Expr arg : args)
        _args.push_back(k_vars[arg][i]);

      side.push_back(bind::fapp(step, _args));

      _args.clear();
    }

    obvPoint[subset] = side;
  }
}

void KPropertyVerifier::getBadExprs(std::map<std::set<int>, ExprVector> &obvPoint,
                                    ExprVector &bad_rules,
                                    Expr post) {
  std::set<int> full_set;
  for (int i = 0; i < hyper_k; i++)
    full_set.insert(i);

  ExprVector side = obvPoint[full_set];
  side.push_back(boolop::lneg(post));

  bad_rules.push_back(boolop::land(side));
}

void KPropertyVerifier::getValidExprs(std::map<std::set<int>, ExprVector> &obvPoint,
                                        std::set<std::set<int>> &k_subsets,
                                        std::map<std::set<int>, Expr> &valid_rules) {
  std::set<int> full_set;
  for (int i = 0; i < hyper_k; i++)
    full_set.insert(i);

  for (std::set<int> subset : k_subsets) {
    ExprVector side;
    Expr res;
    for (Expr e : obvPoint[subset])
      side.push_back(boolop::lneg(e));

    res = boolop::land(side);

    if (subset == full_set)
      res = boolop::lor(res, boolop::land(obvPoint[subset]));

    valid_rules[subset] = res;
  }
}

void KPropertyVerifier::getHyperExprsFromFunction(Function &F, HornifyModule &hm, ExprFactory &m_efac, Module &M,
                                                  hyper_expr_map &k_vars, std::set<std::set<int>> &k_subsets,
                                                  std::map<const Function *, std::map<int, Expr>> &pc_rels,
                                                  HornClauseDB::expr_set_type &pre_rules,
                                                  ExprVector &bad_rules,
                                                  std::map<std::set<int>, Expr> &valid_rules) {
  const LiveSymbols &ls = hm.getLiveSybols(F);
  UfoOpSem m_sem(m_efac, hm, M.getDataLayout());
  std::map<int, Expr> steps = pc_rels[&F];
  std::map<std::set<int>, ExprVector> obvPoint;
  int count = 0;

  Expr pc = bind::intConst(mkTerm<std::string>("flat.pc", m_efac));

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

    // create step(pc,x1,...,xn) for pre
    s.write(pc, mkTerm<expr::mpz_class>(count, m_efac));
    args.push_back(s.read(pc));
    for (const Expr &v : glive)
      args.push_back(s.read(v));
    allVars.insert(++args.begin(), args.end());
    assert(std::all_of(allVars.begin(), allVars.end(), bind::IsConst()));

    count++;

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
      pre_rules.insert(side[0]);

    if (fn->getName().startswith("hyper.post.")) {
      getObservationPointExprs(obvPoint, args, steps, k_subsets, k_vars);
      getBadExprs(obvPoint, bad_rules, side[0]);
      getValidExprs(obvPoint, k_subsets, valid_rules);
    }
  }

  print_obv_exprs(obvPoint);
}

void KPropertyVerifier::getHyperExprsModule(Module &M, HornifyModule &hm, ExprFactory &m_efac,
                                            hyper_expr_map &k_vars, std::set<std::set<int>> &k_subsets,
                                            std::map<const Function *, std::map<int, Expr>> &pc_rels,
                                            HornClauseDB::expr_set_type &pre_rules,
                                            ExprVector &bad_rules,
                                            std::map<std::set<int>, Expr> &valid_rules) {
  for (Function &F : M) {
    if (!F.empty())
      getHyperExprsFromFunction(F, hm, m_efac, M, k_vars, k_subsets, pc_rels,
                                pre_rules, bad_rules, valid_rules);
  }
  print_pre_rules(pre_rules);
  print_bad_rules(bad_rules);
  print_valid_rules(valid_rules);
}

void KPropertyVerifier::getPcRels(const HornClauseDB::expr_set_type &orig_rels,
                                  std::map<const Function *, std::map<int, Expr>> &new_rels,
                                  ExprFactory &m_efac, Module &M) {
  for (Function &F : M) {
    if (F.empty())
      continue;
    Expr name = mkTerm<const Function *>(&F, m_efac);
    if (m_interproc)
      name = variant::prime(name);
    Expr rel = getFunctionRelFromDB(orig_rels, name);
    new_rels[&F] = std::map<int, Expr>();
    for (int i = 0; i < hyper_k; i++) {
      std::string suffix = "_thread_" + std::to_string(i);
      Expr new_name = variant::tag(name, suffix);
      Expr fdecl = bind::rename(rel, new_name);
      new_rels[&F][i] = fdecl;
    }
  }

  print_pc_rels(new_rels);
}

bool KPropertyVerifier::runOnModule(Module &M) {
  ScopedStats _st_("KPropertyVerifier");
  HornifyModule &hm = getAnalysis<HornifyModule>();
  HornClauseDB &db = hm.getHornClauseDB();
  // Need to reset the DB after using it - add a function to reset.
  ExprFactory &m_efac = hm.getExprFactory();
  //EZ3 &z3 = hm.getZContext();

  m_interproc = hm.getInterProc();

  hyper_expr_map k_vars;
  hyper_subset_expr_map doomed_rels;
  std::map<const Function *, std::map<int, Expr>> pc_rels;
  HornClauseDB::expr_set_type pre_rules;
  ExprVector bad_rules;
  std::map<std::set<int>, Expr> valid_rules;

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

  getPcRels(rels, pc_rels, m_efac, M);

  getHyperExprsModule(M, hm, m_efac, k_vars, k_subsets, pc_rels,
                      pre_rules, bad_rules, valid_rules);

  return true;
}

}
