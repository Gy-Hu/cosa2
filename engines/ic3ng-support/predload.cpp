#include "engines/ic3ng.h"

#include <fstream>

#include "smt-switch/smtlib_reader.h"

namespace pono {

void IC3ng::set_helper_term_predicates(const smt::TermVec & preds) {

  solver_->push();
    for (const auto & p : preds) {
      if (!(p->get_sort()->get_sort_kind() == smt::SortKind::BOOL ||
          (p->get_sort()->get_sort_kind() == smt::SortKind::BV && 
           p->get_sort()->get_width() == 1)))
           continue;
      if(solver_->check_sat_assuming({p}).is_unsat())
        continue;
      auto neg_p = smart_not(p);
      if(solver_->check_sat_assuming({neg_p}).is_unsat())
        continue;
      // check init/\not(p)  unsat
      // if (solver_->check_sat_assuming({ts_.init() ,neg_p}).is_unsat())
        loaded_predicates_.push_back(p);

      // if (solver_->check_sat_assuming({ts_.init() ,p}).is_unsat())
        loaded_predicates_.push_back(neg_p);
    }
  solver_->pop();

}

// if  A is a subset (or equal to ) B, returns true
bool static is_subset(const smt::UnorderedTermSet & A, const smt::UnorderedTermSet & B) {
  for (const auto & e : A) {
    if (B.find(e) == B.end())
      return false;
  }
  return true;
}

bool static has_intersection(const smt::UnorderedTermSet & a, const smt::UnorderedTermSet & b) {
  const auto & smaller = a.size() < b.size() ? a : b;
  const auto & other = a.size() < b.size() ? b : a;
  for (const auto & e : smaller)
    if (other.find(e) != other.end())
      return true;
  return false;
}

// s 00 a 0001 b 0011
// s ==00 ->  a > b   a == b a>=b 
unsigned IC3ng::extend_predicates(Model *cex, smt::TermVec & conj_inout) {
  //TODO:
  // for each predicate p:
  //   check if  cex_expr /\ p  is unsat            :   use (p)
  //         or  cex_expr /\ not(p)  is unsat       :   use (not p)
  //   you may only check the case when (cex_expr) and p have shared variables
  //   you don't need to check every time, you can cache this...
  //   you can also cache the result of which p to consider for a given variable set
  
  // make sure newly added preds are put in the beginning of conj_inout

  auto model_info_pos = model_info_map_.find(cex);
  if (model_info_pos == model_info_map_.end()) {
    PerVarInfo * var_info_ = cex->get_per_var_info();
    if (!var_info_->related_info_populated) {
      // TODO: setup related info
      // based on structural varset check
      const smt::UnorderedTermSet & vars_in_cex =
        cex->get_per_var_info()->vars_noslice_in_cex;

      for (const auto & p : loaded_predicates_) {
        smt::UnorderedTermSet vars_in_pred;
        smt::get_free_symbolic_consts(p, vars_in_pred);
        if(is_subset(vars_in_pred, vars_in_cex))
          var_info_->preds_w_subset_vars.push_back(p);
        else if(has_intersection(vars_in_pred, vars_in_cex))
          var_info_->preds_w_related_vars.push_back(p);
      }
      var_info_->related_info_populated = true;
    }

    // compute the predicates to use below
    smt::TermVec predicates_to_use;
    {
      solver_->push();
      solver_->assert_formula(cex->to_expr(solver_));
      for (const auto & p : var_info_->preds_w_subset_vars) {
        auto r = solver_->check_sat_assuming({p});
        if (r.is_unsat())
          predicates_to_use.push_back(smart_not(p));
      }
      if (predicates_to_use.empty()) {
        for (const auto & p : var_info_->preds_w_related_vars) {
          auto r = solver_->check_sat_assuming({p});
          if (r.is_unsat())
            predicates_to_use.push_back(smart_not(p));
        }
      } // end of if predicates_to_use.empty()
      solver_->pop();
    }
    // TODO: from preds_w_subset_vars -> PerCexInfo::preds_to_use
    //  solve sat?
    auto res = model_info_map_.emplace(cex, PerCexInfo(std::move(predicates_to_use)));
    model_info_pos = res.first;
  }
  auto preds = model_info_pos->second.preds_to_use;
  auto num_preds = preds.size();

  // Check if preds is empty
  if (num_preds == 0) {
    // Handle the case where no predicates are available
    // For example, we might keep conj_inout unchanged or provide default predicates
    return 0; // Early return or provide default handling
  }

  preds.insert(preds.end(), conj_inout.begin(), conj_inout.end() );
  // careful: when external predicates is null -> cause `predicates_to_use` vector is empty
  // so, leads to an empty `conj_inout` after `swap`
  conj_inout.swap(preds);
  return num_preds;
} // end of extend_predicates

} // namespace pono

