#include "seahorn/KPropertyVerifier.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornClauseDB.hh"

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

static ExprVector makeNewVars(const ExprVector &vars, int k) {
  // TODO
  return vars;
}

static HornClauseDB::expr_set_type makeDoomedRels(ExprVector &vars, int k) {
    return HornClauseDB::expr_set_type();
}

static ExprVector getHyperExprs(enum HyperProperties) {
  return ExprVector();
}

bool KPropertyVerifier::runOnModule(Module &M) {
  ScopedStats _st_("KPropertyVerifier");
  HornifyModule &hm = getAnalysis<HornifyModule>();

  HornClauseDB &db = hm.getHornClauseDB();
  ExprFactory &efac = hm.getExprFactory();

  const ExprVector &vars = db.getVars();
  const HornClauseDB::RuleVector &rules = db.getRules();
  const HornClauseDB::expr_set_type &rels = db.getRelations();

  ExprVector k_vars = makeNewVars(vars, hyper_k);
  HornClauseDB::expr_set_type doomed_rels = makeDoomedRels(k_vars, hyper_k);
  ExprVector pre_exprs = getHyperExprs(PRE);

  return true;
}

}
