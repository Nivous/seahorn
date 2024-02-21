#include "seahorn/KPropertyVerifier.hh"
#include "seahorn/UfoOpSem.hh"
#include "seahorn/Support/ExprSeahorn.hh"
#include "seahorn/Support/CFG.hh"
#include "seahorn/Expr/ExprNumericUtils.hh"

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

static void print_vars(const Function *F, hyper_expr_map *k_vars) {
  errs() << "The new variables for function: " << F->getName() << "\n";
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

static void print_duplicated_pc_rels(const Function *F, std::map<int, Expr> &new_rels) {
  errs() << "The new duplicated pc rels for function: " << F->getName() << "\n";
  for(std::map<int, Expr>::iterator it2 = new_rels.begin(); it2 != new_rels.end(); ++it2) {
    errs() << "i = " << it2->first << " : " << "\n";
    Expr decl = it2->second;
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

static void print_combined_pc_rels(const Function *F, Expr new_rel) {
  Expr decl = new_rel;
  errs() << "The new combined pc rels for function: " << F->getName() << "\n";
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

static void print_obv_exprs(const Function *F, std::map<std::set<int>, ExprVector> &obvPoint) {
  errs() << "Observation points expressions for function: " << F->getName() << "\n";
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

static void print_valid_rules(const Function *F, std::map<std::set<int>, Expr> &valid_rules) {
  errs() << "Valid expressions for function: " << F->getName() << "\n";
  for (std::map<std::set<int>, Expr>::iterator it = valid_rules.begin(); it != valid_rules.end(); it++) {
    errs() << "Valid expressions for subset: ";
    for (int i: it->first) {
      errs() << i << "_";
    }
    errs() << "\n" << *(it->second) << "\n";
  }
}

static void print_bad_rules(const Function *F, ExprVector &bad_rules) {
  errs() << "Bad expressions for function: " << F->getName() << "\n";
  errs() << "The bad rules are:\n";
  for (Expr e : bad_rules)
    errs() << *e << "\n";
}

static void print_pre_rules(const Function *F, HornClauseDB::expr_set_type &pre_rules) {
  errs() << "Pre expressions for function: " << F->getName() << "\n";
  errs() << "Pre rules are:\n";
  for (Expr e : pre_rules)
    errs() << *e << "\n";
}

static void print_trace_info(const Function *F, std::map<std::pair<int, int>, ExprVector[3]> &trace_info) {

  if (F->hasName())
    errs() << "Trace info for function: " << F->getName() << "\n";
  else {
    errs() << "Function:\n";
    F->print(errs());
  }
  for (std::map<std::pair<int, int>, ExprVector[3]>::iterator it2 = trace_info.begin();
        it2 != trace_info.end();
        it2++) {
    errs() << "Trace rule moving from src_bb_count = " << it2->first.first;
    errs() << " and dst_bb_count = " << it2->first.second << " :\n";
    errs() << "Args for source = {";
    for (int i = 0; (unsigned int)i < it2->second[0].size(); i++) {
      errs() << *(it2->second[0][i]);
      if ((unsigned int)i != it2->second[0].size() - 1)
        errs() << ", ";
    }
    errs() << "}\n";
    errs() << "Logic formulas during block:\n";
    for (int i = 0; (unsigned int)i < it2->second[1].size(); i++)
      errs() << *(it2->second[1][i]) << "\n";
    errs() << "Args for destination = {";
    for (int i = 0; (unsigned int)i < it2->second[2].size(); i++) {
      errs() << *(it2->second[2][i]);
      if ((unsigned int)i != it2->second[2].size() - 1)
        errs() << ", ";
    }
    errs() << "}\n";
  }
}

static void print_trace_rules(const Function *F, std::map<std::pair<int, int>, std::map<int, Expr>> &trace_rules) {
  if (F->hasName())
    errs() << "Trace Rules for function: " << F->getName() << "\n";
  else {
    errs() << "Function:\n";
    F->print(errs());
  }
  for (std::map<std::pair<int, int>, std::map<int, Expr>>::iterator it2 = trace_rules.begin();
        it2 != trace_rules.end();
        it2++) {
    errs() << "Trace rules moving from src_bb_count = " << it2->first.first;
    errs() << " and dst_bb_count = " << it2->first.second << " :\n";
    for (std::map<int, Expr>::iterator it3 = it2->second.begin(); it3 != it2->second.end(); it3++) {
      if (it3->second) {
        errs() << "thread number = " << it3->first << ":\n";
        errs() << *(it3->second) << "\n";
      }
    }
  }
}

/**
 * @brief Get the Args From Fapp object
 *
 * @param e The FAPP expr
 * @param rel The fdecl that the fapp is supposed to be an application of
 * @param args the vector that will contain the arguments of the fapp
 * @return  >= 0 if the fapp is an application of fdecl
 *          -1 otherwise
 */
static int getArgsFromFapp(Expr e, Expr rel, ExprVector &args) {
  if (e->left() != rel)
    return -1;

  args.reserve(e->arity() - 1);
  args.insert(args.begin(), ++(++(e->args_begin())), e->args_end());

  Expr pc = *(++(e->args_begin()));
  expr::mpz_class num;
  if (!expr::numeric::getNum(pc, num))
    return -1;

  return std::stoi(num.to_string(10));
}

/**
 * @brief Get the Args From Body clause
 *
 * @param e the head clause we want to extract the arguments from
 * @param rel the relation that match the function we are currently looking at
 * @param args1 vector to contain the arguments of the fapp in the body
 * @param args2 vector to contain the operations in the body clause
 * @return  > 0 the pc matching the fapp in the body clause if it is of type rel
 *          -1 otherwise or if something fails
 */
static int getArgsFromBody(Expr e, Expr rel, ExprVector &args1, ExprVector &args2) {
  int pc = -1;
  // Expect first argument in AND clause to be FAPP of the body clause or to be only an Fapp
  if ((e->arity() == 2) && isOpX<AND>(e)) {
    pc = getArgsFromFapp(e->left(), rel, args1);
    if (pc < 0)
      return -1;

    Expr narry_and = e->right();
    if (!isOpX<AND>(narry_and))
      return -1;

    args2.reserve(narry_and->use_count());
    args2.insert(args2.begin(), narry_and->args_begin(), narry_and->args_end());
  } else if(bind::isFapp(e))
    pc = getArgsFromFapp(e, rel, args1);

  return pc;
}

/**
 * @brief Convert singular expression to use variables variants from thread i
 *
 * @param e the original expression
 * @param k_vars the map var -> var from thread i
 * @param i the number of the thread
 * @return the new expression
 */
static Expr getConvertedExprFromExpr(Expr e, hyper_expr_map &k_vars, int i) {
  if (!e)
    return Expr(0);

  // Handle constants
  if (isOpX<TRUE>(e) || isOpX<FALSE>(e) || isOpX<MPZ>(e))
    return e;

  if (k_vars.find(e) != k_vars.end())
    return k_vars[e][i];

  ExprVector side;
  for (int j = 0; (unsigned int)j < e->arity(); j++)
    side.push_back(getConvertedExprFromExpr(e->arg(j), k_vars, i));

  return expr::mknary(e->op(), side.begin(), side.end());
}

/**
 * @brief Get the Combined Expr from Narry AND expression.
 * Also changes the variables to use variables variants from thread i.
 *
 * @param narry_and the ExprVector containing all expressions used in the Narry AND
 * @param k_vars the map var -> var from thread i
 * @param i number of the thread
 * @return The combined expression
 */
static Expr getConvertedExprFromNarryAnd(ExprVector &narry_and, hyper_expr_map &k_vars, int i) {
  ExprVector side; // Will hold the converted expressions

  for (Expr e : narry_and)
    side.push_back(getConvertedExprFromExpr(e, k_vars, i));

  if (side.size() > 0)
    return boolop::land(side);

  return Expr(0);
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

static Expr getDestinationPC(Expr e) {
  // Expect first argument in AND clause to be FAPP we are looking for.
  if ((e->arity() != 2) || !isOpX<AND>(e))
    return Expr(0);

  Expr fapp_e = e->left();
  if (!bind::isFapp(fapp_e) || bind::domainSz(fapp_e) < 1)
    return Expr(0);

  auto fappArgs = fapp_e->args_begin();
  std::advance(fappArgs, 1); // note: the first child is the fdecl

  return *fappArgs;
}

void KPropertyVerifier::makeHyperVars(const Function *F, const ExprVector &vars, ExprFactory &m_efac, Module &M,
                                      hyper_expr_map &k_vars, ExprVector &all_k_vars) {
  int i;
  Expr new_var;

  for (const Expr &var : vars) {
    std::stringstream st;
    st << *bind::fname(var->left());
    std::string var_name = st.str();
    std::string func_name = F->getName().str();
    if (var_name.find(func_name) == std::string::npos)
      continue;

    k_vars.insert(std::pair<Expr, std::map<int, Expr>>(var, std::map<int, Expr>()));
    for (i = 0; i < hyper_k; i++) {
      Expr fdecl = bind::fname(var);
      Expr fname = bind::fname(fdecl);
      fname = variant::tag(fname, "_thread_" + std::to_string(i));
      Expr new_var = bind::reapp(var, bind::rename(fdecl, fname));
      k_vars[var].insert(std::pair<int, Expr>(i, new_var));
      all_k_vars.push_back(new_var);
    }
  }

  print_vars(F, &k_vars);
}

void KPropertyVerifier::makeDoomedRels(hyper_expr_map &vars, Function *fn,
                                        std::set<std::set<int>> &k_subsets, ExprFactory &m_efac,
                                        hyper_subset_expr_map *doomed_rels) {
  ExprVector sorts;
  Expr orig_name = mkTerm<const Function *>(fn, m_efac);
  Expr name;
  std::string suffix;
  Expr pc = bind::intConst(mkTerm<std::string>("flat.pc", m_efac));

  for (int i = 0; i < hyper_k; i++)
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

void KPropertyVerifier::getHyperExprsFromFunction(const Function *F, HornifyModule &hm, ExprFactory &m_efac, Module &M,
                                                  hyper_expr_map &k_vars, std::set<std::set<int>> &k_subsets,
                                                  std::map<int, Expr> &pc_rels,
                                                  HornClauseDB::expr_set_type &pre_rules,
                                                  ExprVector &bad_rules,
                                                  std::map<std::set<int>, Expr> &valid_rules,
                                                  int *max_pc) {
  const LiveSymbols &ls = hm.getLiveSybols(*F);
  UfoOpSem m_sem(m_efac, hm, M.getDataLayout());
  std::map<int, Expr> steps = pc_rels;
  std::map<std::set<int>, ExprVector> obvPoint;
  int count = 0;

  Expr pc = bind::intConst(mkTerm<std::string>("flat.pc", m_efac));

  // globally live
  ExprSet glive;

  for (auto &BB : *F) {
    auto &live = ls.live(&BB);
    glive.insert(live.begin(), live.end());
  }

  ExprSet allVars;
  ExprVector args;
  SymStore s(m_efac);

  for (const Expr &v : glive)
    args.push_back(s.read(v));
  allVars.insert(args.begin(), args.end());

  for (auto &BB : *F) {
    const BasicBlock *bb = &BB;
    for (const BasicBlock *dst : succs(*bb)) {
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

      // TODO: Implement more hyper functions
      // Analyze block
      ExprVector side;
      m_sem.execEdg(s, BB, *dst, side);
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

        *max_pc = count;
      }
    }

    count++;
  }
  print_obv_exprs(F, obvPoint);
  print_pre_rules(F, pre_rules);
  print_bad_rules(F, bad_rules);
  print_valid_rules(F, valid_rules);
}

/**
 * @brief This function should create the new relations we need for validating k-properties.
 * We are using flat conifugration only for now, so there is one relation which controls the flow of the function.
 * We are going to duplicate this relation for each of the threads.
 * We are also going to create a new relation which will determine the flow of all threads together.
 *
 * @param orig_rels All the relations generate by the hornify module pass.
 * @param new_rels One of the outputs of the function. Will hold the individual duplicated relations for each thread
 * It will hold a maps i -> relation of thread i
 * @param m_efac Expr factory
 * @param M The Functino
 * @param k_rels One of the outputs of the function. Will hold the individual duplicated relations for each thread.
 * It will hold a map between the original relation to another map which maps i -> relation of thread i
 * @param pc_combined_rel One of the outputs of the function. Will hold the combined relations for all the threads
 * It will hold a map between the function to the relevant relation
 */
void KPropertyVerifier::getPcRels(const Function *F, const HornClauseDB::expr_set_type &orig_rels,
                                  std::map<int, Expr> &new_rels, ExprFactory &m_efac, hyper_expr_map &k_rels,
                                  Expr pc_combined_rel) {
  // Getting the name of the relation as created in hornify module pass
  Expr name = mkTerm<const Function *>(F, m_efac);
  if (m_interproc)
    name = variant::prime(name);

  Expr rel = getFunctionRelFromDB(orig_rels, name);
  k_rels[rel] = std::map<int, Expr>();

  // Creating the individual duplicated relations
  for (int i = 0; i < hyper_k; i++) {
    std::string suffix = "_thread_" + std::to_string(i);
    Expr new_name = variant::tag(name, suffix);
    Expr fdecl = bind::rename(rel, new_name);
    new_rels[i] = fdecl;
    k_rels[rel][i] = fdecl;
  }

  // Creating the combined relation
  ExprVector sorts;
  for (int i = 0; (unsigned int)i < bind::domainSz(rel); i++) {
    for (int j = 0; j < hyper_k; j++) {
      sorts.push_back(bind::domainTy(rel, i));
    }
  }

  sorts.push_back(mk<BOOL_TY>(m_efac));
  Expr new_name = variant::tag(name, "hyper");
  Expr fdecl = bind::fdecl(new_name, sorts);
  pc_combined_rel = fdecl;

  print_duplicated_pc_rels(F, new_rels);
  print_combined_pc_rels(F, pc_combined_rel);
}

/**
 * @brief Get the Trace Info from the module
 * As described in the main function of the pass the trace info contains the following:
 * a map: (src_bb_count, dst_bb_count) -> 3 Expr Vectors
 * The first expr vector contains the variables used for the fapp in the src_bb_count block of function f
 * the second expr vector contains all the logic formulas derived from this block during hornify module pass
 * The third expr vector contains the variables used for the fapp in the dst_bb_count block of function f
 *
 * @param M The module object
 * @param trace_info the output of the function, as described above
 * @param orig_rels The original relations from the horinfy module pass
 * @param m_efac  Expr factory
 * @param rules the original rules from the hornify module pass
 */
void KPropertyVerifier::getTraceInfo(const Function *F, std::map<std::pair<int, int>, ExprVector[3]> &trace_info,
                                      const HornClauseDB::expr_set_type &orig_rels, ExprFactory &m_efac,
                                      const HornClauseDB::RuleVector &rules) {
  // Getting the name of the relation as created in hornify module pass
  Expr name = mkTerm<const Function *>(F, m_efac);
  if (m_interproc)
    name = variant::prime(name);

  Expr rel = getFunctionRelFromDB(orig_rels, name);

  for (HornRule rule : rules) {
    int dst_bb_count = -1, src_bb_count;
    Expr head = rule.head();
    Expr body = rule.body();

    ExprVector args1;
    ExprVector args2;
    ExprVector args3;

    if (bind::isFapp(head))
      dst_bb_count = getArgsFromFapp(head, rel, args3);

    if (dst_bb_count < 0)
      continue;

    src_bb_count = getArgsFromBody(body, rel, args1, args2);
    if (src_bb_count < 0)
      continue;

    trace_info[std::pair<int,int>(src_bb_count, dst_bb_count)][0] = args1;
    trace_info[std::pair<int,int>(src_bb_count, dst_bb_count)][1] = args2;
    trace_info[std::pair<int,int>(src_bb_count, dst_bb_count)][2] = args3;
  }

  print_trace_info(F, trace_info);
}

/**
 * @brief The purpose of this function is to process the rules in trace info for k-safety.
 * The function should duplicate the rules but change each variable to the mathcing variable in thread i.
 *
 * @param trace_info the trace info already extracted, which contains the rules
 * @param k_vars the map var -> var from thread i
 * @param trace_rules the output of the function. the new mapping of rules to Expr that uses the relevant variables
 */
void KPropertyVerifier::getTraceRulesFromInfo(const Function *F,
                            std::map<std::pair<int, int>, ExprVector[3]> &trace_info, hyper_expr_map &k_vars,
                            std::map<std::pair<int, int>, std::map<int, Expr>> &trace_rules) {
  for (std::map<std::pair<int, int>, ExprVector[3]>::iterator it2 = trace_info.begin();
        it2 != trace_info.end();
        it2++) {
    if (it2->second[1].size() == 0)
      continue;

    int src_bb_count = it2->first.first;
    int dst_bb_count = it2->first.second;
    trace_rules[std::pair<int, int>(src_bb_count, dst_bb_count)] = std::map<int, Expr>();
    for (int i = 0; i < hyper_k; i++)
      trace_rules[std::pair<int, int>(src_bb_count, dst_bb_count)][i] =
        getConvertedExprFromNarryAnd(it2->second[1], k_vars, i);
  }

  print_trace_rules(F, trace_rules);
}


void KPropertyVerifier::getTraceRules(const Function *F, ExprVector &all_k_vars, hyper_expr_map &k_vars,
                                      hyper_expr_map &k_rels,
                                      std::set<std::set<int>> &k_subsets,
                                      std::map<std::pair<int, int>, ExprVector[3]>& trace_info,
                                      hyper_subset_expr_map &doomed_rels,
                                      std::map<std::pair<int, int>, std::map<int, Expr>> &trace_rules,
                                      int max_pc,
                                      std::map<std::pair<int, int>, std::map<std::set<int>, Expr>> &final_trace_rules) {

}

bool KPropertyVerifier::runOnModule(Module &M) {
  ScopedStats _st_("KPropertyVerifier");
  HornifyModule &hm = getAnalysis<HornifyModule>();

    if (hm.getStepSize() != hm_detail::FLAT_SMALL_STEP) {
    errs() << "Currently hyper properties supports only flat small step [step = " << hm.getStepSize() << " ].\n";
    return true;
  }

  HornClauseDB &db = hm.getHornClauseDB();
  const ExprVector &vars = db.getVars();
  const HornClauseDB::RuleVector &rules = db.getRules();
  const HornClauseDB::expr_set_type &rels = db.getRelations();

  struct functionResultAggregator out;

  m_interproc = hm.getInterProc();
  ExprFactory &m_efac = hm.getExprFactory();

  std::set<std::set<int>> k_subsets = generateAllSubsets(hyper_k);

  for (Function &F : M) {
    // Skip empty functions
    if (F.empty())
      continue;
    
    runOnFunction(&F, m_efac, vars, rules, rels, k_subsets, hm, M, &out);
  }

  db.resetDB();

  for (Expr rel: out.relations)
    db.registerRelation(rel);

  for (HornRule rule: out.rules)
    db.addRule(rule);
  
  return true;
}

void KPropertyVerifier::runOnFunction(const Function *F, ExprFactory &m_efac, const ExprVector &vars,
                                      const HornClauseDB::RuleVector &rules, const HornClauseDB::expr_set_type &rels,
                                      std::set<std::set<int>> &k_subsets, HornifyModule &hm, Module &M,
                                      struct functionResultAggregator *out)
{
  /* maps variable -> (map i-> variable variant in thread i) */
  hyper_expr_map k_vars;
  /* maps relation -> (map i-> relation variant in thread i) */
  hyper_expr_map k_rels;
  /* all doomed relations */
  hyper_subset_expr_map doomed_rels;
  /* maps i -> function relation variant of thread i */
  std::map<int, Expr> pc_rels;
  /* combined relation for all threads for this function*/
  Expr pc_combined_rel;
  /* all pre rules */
  HornClauseDB::expr_set_type pre_rules;
  /* all bad rules */
  ExprVector bad_rules;
  /* maps subset of k -> valid expression for this subset */
  //TODO:: We might have an issue with this expression
  std::map<std::set<int>, Expr> valid_rules;
  /* all variables variants for this function */
  ExprVector all_k_vars;
  /* maximum pc for this function*/
  int max_pc_for_function;

  /* This map should hold the final trace rules in the reduction
  (src_bb_count, dst_bb_count) -> (subset -> rule) */
  std::map<std::pair<int, int>, std::map<std::set<int>, Expr>> final_trace_rules;

  /* The first type of expression in the reduction:
  All threads are doomed and pre => bottom*/
  Expr doomed_pre_expr;

  /* This maps (src_bb_count, dst_bb_count) ->
  (variables at entry, trace rules in block, variables at exit) */
  std::map<std::pair<int, int>, ExprVector[3]> trace_info;

  /* This maps (src_bb_count, dst_bb_count) ->
  map from 0 <= i < k to the relevant trace rule from trace info in thread i variants */
  std::map<std::pair<int, int>, std::map<int, Expr>> trace_rules;

  makeHyperVars(F, vars, m_efac, M, k_vars, all_k_vars); /* Get new vars */

  /* Insert doomed state function to symbol table */
  std::string doomed_name = std::string(DOOMED_STATE_FUNCTION_NAME) + std::string("_") + F->getName().str();
  auto FC = M.getOrInsertFunction(doomed_name, Type::getVoidTy(M.getContext()));
  auto *FN = dyn_cast<Function>(FC.getCallee());

  makeDoomedRels(k_vars, FN, k_subsets, m_efac, &doomed_rels);

  getPcRels(F, rels, pc_rels, m_efac, k_rels, pc_combined_rel);

  getHyperExprsFromFunction(F, hm, m_efac, M, k_vars, k_subsets, pc_rels,
                            pre_rules, bad_rules, valid_rules, &max_pc_for_function);

  getTraceInfo(F, trace_info, rels, m_efac, rules);

  getTraceRulesFromInfo(F, trace_info, k_vars, trace_rules);

  //getDoomedPreExpr(pre_rules, doomed_rels, all_k_vars, )

  getTraceRules(F, all_k_vars, k_vars, k_rels, k_subsets, trace_info, doomed_rels, trace_rules,
                max_pc_for_function, final_trace_rules);  
}

}
