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
  PerVarInfo * var_info = cex->get_per_var_info();  

  if (model_info_pos == model_info_map_.end()) {
     // TODO: setup related info
    // based on structural varset check
    if (!var_info->related_info_populated) {
      const smt::UnorderedTermSet & vars_in_cex =
        cex->get_per_var_info()->vars_noslice_in_cex;

      for (const auto & p : loaded_predicates_) {
        smt::UnorderedTermSet vars_in_pred;
        smt::get_free_symbolic_consts(p, vars_in_pred);
        
        // First check if it has any intersection with cex vars
        if(has_intersection(vars_in_pred, vars_in_cex)) {
          // Then check if it's a complete subset
          if(is_subset(vars_in_pred, vars_in_cex)) {
            var_info->preds_w_subset_vars.push_back(p);
          } else {
            // Has intersection but not subset - these are the related vars
            var_info->preds_w_related_vars.push_back(p);
          }
        }
      }
      var_info->related_info_populated = true;
    }

    // Calculate predicates to use
    smt::TermVec predicates_to_use;
    {
      solver_->push();
      auto cex_formula = cex->to_expr(solver_);
      solver_->assert_formula(cex_formula);

      // First check subset vars, double check
      for (const auto & p : var_info->preds_w_subset_vars) {
        // check p
        smt::TermVec assumptions;
        assumptions.push_back(p);
        auto r1 = solver_->check_sat_assuming(assumptions);
        if (r1.is_unsat()) {
          predicates_to_use.push_back(smart_not(p));
          continue;
        }
        // check not(p)
        assumptions.clear();
        assumptions.push_back(smart_not(p));
        auto r2 = solver_->check_sat_assuming(assumptions);
        if (r2.is_unsat()) {
          predicates_to_use.push_back(p);
        }
      }

      // always handle related vars, no matter how many subset vars found
      const auto & vars_in_cex = cex->get_per_var_info()->vars_noslice_in_cex;
      for (const auto & p : var_info->preds_w_related_vars) {
        // achieve the vars in p but not in cex
        smt::UnorderedTermSet vars_in_pred;
        smt::get_free_symbolic_consts(p, vars_in_pred);
        smt::UnorderedTermSet external_vars;
        for (const auto & v : vars_in_pred) {
          if (vars_in_cex.find(v) == vars_in_cex.end()) {
            external_vars.insert(v);
          }
        }

        // Try different values for each external variable
        bool found_useful = false;
        for (const auto & ext_var : external_vars) {
          // Get the sort of the variable
          auto var_sort = ext_var->get_sort();
          
          // Try special values based on the bit-width
          std::vector<int64_t> test_values;
          if (var_sort->get_sort_kind() == smt::BV) {
            uint32_t width = var_sort->get_width();
            test_values = {0, 1};  // Always safe values
            if (width > 1) {
              test_values.push_back((1ll << (width-1)) - 1);  // Maximum positive value
              test_values.push_back(-(1ll << (width-1)));     // Minimum negative value
            }
          } else {
            // For non-bitvector sorts, use simple values
            test_values = {0, 1, -1};
          }
          
          for (auto val : test_values) {
            try {
              // Create a constant of appropriate width
              auto const_val = solver_->make_term(val, var_sort);
              
              // Create substitution map
              smt::UnorderedTermMap subst_map;
              subst_map[ext_var] = const_val;
              
              // Create terms vector with single term
              smt::TermVec terms;
              terms.push_back(p);
              
              // Replace the external variable
              auto subst_terms = solver_->substitute_terms(terms, subst_map);
              auto subst_p = subst_terms[0];  // We only substituted one term
              
              // Check the substituted predicate (bi-directional check)
              smt::TermVec assumptions;
              assumptions.push_back(subst_p);
              auto r1 = solver_->check_sat_assuming(assumptions);
              if (r1.is_unsat()) {
                predicates_to_use.push_back(smart_not(subst_p));
                found_useful = true;
                break;
              }
              
              assumptions.clear();
              assumptions.push_back(smart_not(subst_p));
              auto r2 = solver_->check_sat_assuming(assumptions);
              if (r2.is_unsat()) {
                predicates_to_use.push_back(subst_p);
                found_useful = true;
                break;
              }
            } catch (const std::exception & e) {
              // If we get an exception creating the constant, skip this value
              continue;
            }
          }
          
          if (found_useful) break;
        }
      }
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

  preds.insert(preds.end(), conj_inout.begin(), conj_inout.end());
  // careful: when external predicates is null -> cause `predicates_to_use` vector is empty
  // so, leads to an empty `conj_inout` after `swap`
  conj_inout.swap(preds);

  // print all the predicates
  std::cout << "\n=== Extended Predicates Analysis ===\n";
  
  // Print variables in cex
  const auto & vars_in_cex = cex->get_per_var_info()->vars_noslice_in_cex;
  std::cout << "Variables in counterexample:\n";
  for (const auto & v : vars_in_cex) {
    std::cout << "  " << v->to_string() << " [sort: " << v->get_sort()->to_string() << "]\n";
  }

  // Print original predicates
  std::cout << "\nOriginal predicates from external source:\n";
  for (const auto & p : loaded_predicates_) {
    std::cout << "  " << p->to_string() << "\n";
  }

  // Print subset vars predicates
  std::cout << "\nPredicates with subset vars (vars fully in cex):\n";
  for (const auto & p : var_info->preds_w_subset_vars) {
    // Get variables in this predicate
    smt::UnorderedTermSet vars_in_pred;
    smt::get_free_symbolic_consts(p, vars_in_pred);
    
    std::cout << "  Pred: " << p->to_string() << "\n";
    std::cout << "    Variables: ";
    for (const auto & v : vars_in_pred) {
      std::cout << v->to_string() << " ";
    }
    std::cout << "\n";
  }

  // Print related vars predicates and their substitutions
  std::cout << "\nPredicates with related vars:\n";
  for (const auto & p : var_info->preds_w_related_vars) {
    // Get variables in this predicate
    smt::UnorderedTermSet vars_in_pred;
    smt::get_free_symbolic_consts(p, vars_in_pred);
    
    std::cout << "  Pred: " << p->to_string() << "\n";
    std::cout << "    All vars: ";
    for (const auto & v : vars_in_pred) {
      std::cout << v->to_string() << " ";
    }
    std::cout << "\n    External vars: ";
    for (const auto & v : vars_in_pred) {
      if (vars_in_cex.find(v) == vars_in_cex.end()) {
        std::cout << v->to_string() << " ";
      }
    }
    std::cout << "\n";
  }

  // Print final selected predicates
  std::cout << "\nFinal selected predicates:\n";
  for (const auto & p : conj_inout) {
    std::cout << "  " << p->to_string() << "\n";
  }

  std::cout << "\nTotal predicates selected: " << num_preds << "\n";
  std::cout << "================================\n\n";
  
  return num_preds;
} // end of extend_predicates

} // namespace pono
