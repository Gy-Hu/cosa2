#include "engines/ic3ng.h"

#include <chrono>
#include <fstream>

#include "smt-switch/smtlib_reader.h"
#include "utils/logger.h"
#include "smt-switch/logging_solver.h"

namespace pono {

void IC3ng::set_helper_term_predicates(const smt::TermVec & preds) {

  solver_->push();
  disable_all_labels();
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

void IC3ng::set_helper_term_clauses(const smt::TermVec & clauses) {
  // Store validated clauses
  
  logger.log(1, "Starting to validate {} external clauses", clauses.size());
  
  for (const auto & clause : clauses) {
    // check type
    // HZ: some SMT solvers (e.g. Boolector), does not distinguish
    // Bool vs. BV of width 1
    if ( (clause->get_sort()->get_sort_kind() != smt::SortKind::BOOL) &&
         !(clause->get_sort()->get_sort_kind() == smt::SortKind::BV &&
           clause->get_sort()->get_width() == 1 )) {
      logger.log(2, "Clause {} is not boolean type, skipping", clause);
      continue;
    }

    // check init =>  c?
    // HZ: the clause we load should contain a "NOT" itself
    solver_->push();
    disable_all_labels();
    solver_->assert_formula(ts_.init());
    solver_->assert_formula(smart_not(clause));
    auto r = solver_->check_sat();
    solver_->pop();
    if (!r.is_unsat()) {
      logger.log(2, "Clause {} does not cover initial states, skipping", clause);
      continue;
    } // HZ: it must be unsat

    // check:  init & T => clause' ?
    // HZ: no need to have clause in the previous frame
    //     because init => clause
    solver_->push();
    disable_all_labels();
    solver_->assert_formula(ts_.init());
    solver_->assert_formula(ts_.trans());
    smt::Term next_clause = ts_.next(clause);
    solver_->assert_formula(smart_not(next_clause));
    r = solver_->check_sat();
    solver_->pop();

    if (r.is_unsat()) {
      // clause is inductive
      loaded_clauses_.push_back(clause);
      logger.log(2, "Added valid clause: {}", clause);

      // if frames is not empty, add clause to F₀
      if (!frames.empty()) {
        // Create new lemma, marked as FromSideLoad source
        auto lemma = new_lemma(clause, 
                              nullptr,  // External clauses have no counterexamples
                              LCexOrigin::FromSideLoad());
        
        logger.log(1, "Adding clause to initial frame: {}", clause->to_string());
        // add to F1 // 0 is for init, it should be on F1
        add_lemma_to_frame(lemma, 1);

        // HZ: I don't see the reason for doing this. So I remove it.
        // assert it as a valid invariant to solver
        // solver_->assert_formula(clause);
      } else {
        // HZ: I think you may want to throw an exception
        // because normally this should not happen
        throw PonoException("Frames not initialized yet, clause will be stored in loaded_clauses_");
      }
    } else {
      logger.log(2, "Clause {} fails to cover reachable states at F1, skipping", clause);
    }
  } // end of for each clause
  
  logger.log(1, 
             "Loaded {} valid clauses out of {} total clauses",
             loaded_clauses_.size(),
             clauses.size());
} // end of IC3ng::set_helper_term_clauses

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
static double total_extend_pred_time_ms = 0;
static unsigned total_extend_pred_calls = 0;

unsigned IC3ng::extend_predicates(Model *cex, smt::TermVec & conj_inout) {
  auto t_start = std::chrono::steady_clock::now();
  auto model_info_pos = model_info_map_.find(cex);
  PerUnslicedVarInfo * var_info = cex->get_per_unslicedvar_info();

  if (model_info_pos == model_info_map_.end()) {
    if (!var_info->related_info_populated) {
      const smt::UnorderedTermSet & vars_in_cex =
        cex->get_varset_unslice();

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
      } // end of for each load_predicates_
      var_info->related_info_populated = true;
    }

    // Calculate predicates to use
    smt::TermVec predicates_to_use;
    {
      solver_->push();
      disable_all_labels();
      solver_->assert_formula(cex->to_expr(solver_));

      // DEBUG: print cex details to understand partial vs complete assignment
      logger.log(1, "[extend_pred] === DEBUG: cex analysis ===");
      logger.log(1, "[extend_pred] cex conjs (partial cube):");
      for (const auto & eq : cex->to_expr_conj()) {
        logger.log(1, "[extend_pred]   {}", eq->to_string());
      }
      const auto & vars_in_cex_dbg = cex->get_varset_unslice();
      logger.log(1, "[extend_pred] #vars in cex (unsliced): {}", vars_in_cex_dbg.size());
      logger.log(1, "[extend_pred] #subset_var preds: {}, #related_var preds: {}",
                 var_info->preds_w_subset_vars.size(), var_info->preds_w_related_vars.size());

      // Use check_sat_assuming (old correct method) for subset vars
      for (const auto & p : var_info->preds_w_subset_vars) {
        auto r_pos = solver_->check_sat_assuming({p});
        if (r_pos.is_unsat()) {
          // cex ⊨ ¬p
          predicates_to_use.push_back(smart_not(p));
          logger.log(1, "[extend_pred] subset pred IMPLIED ¬p: {}", p->to_string());
          continue;
        }
        auto r_neg = solver_->check_sat_assuming({smart_not(p)});
        if (r_neg.is_unsat()) {
          // cex ⊨ p
          predicates_to_use.push_back(p);
          logger.log(1, "[extend_pred] subset pred IMPLIED p: {}", p->to_string());
        } else {
          // cex does NOT determine p — this is the partial assignment issue!
          logger.log(1, "[extend_pred] subset pred NOT DETERMINED (partial cex!): {}", p->to_string());
          // DEBUG: show which vars in p are missing from cex
          smt::UnorderedTermSet vars_in_pred;
          smt::get_free_symbolic_consts(p, vars_in_pred);
          for (const auto & v : vars_in_pred) {
            bool in_cex = vars_in_cex_dbg.find(v) != vars_in_cex_dbg.end();
            logger.log(1, "[extend_pred]   var {} in_cex={}", v->to_string(), in_cex);
          }
        }
      }

      // Handle related vars: use check_sat_assuming for correctness
      const auto & vars_in_cex = cex->get_varset_unslice();
      for (const auto & p : var_info->preds_w_related_vars) {
        smt::UnorderedTermSet vars_in_pred;
        smt::get_free_symbolic_consts(p, vars_in_pred);

        // Substitute external vars with their model values
        // First need a SAT call to get values
        auto sat_result = solver_->check_sat();
        if (!sat_result.is_sat()) continue;

        smt::UnorderedTermMap subst_map;
        for (const auto & v : vars_in_pred) {
          if (vars_in_cex.find(v) == vars_in_cex.end()) {
            try {
              subst_map[v] = solver_->get_value(v);
            } catch (const std::exception &) {
              continue;
            }
          }
        }
        if (subst_map.empty()) continue;

        try {
          auto subst_p = solver_->substitute(p, subst_map);
          subst_p = solver_->simplify_term(subst_p);

          // Use check_sat_assuming to verify implication, not just get_value
          auto r_pos = solver_->check_sat_assuming({subst_p});
          if (r_pos.is_unsat()) {
            predicates_to_use.push_back(smart_not(subst_p));
            logger.log(1, "[extend_pred] related pred IMPLIED ¬subst_p: {} (from {})", subst_p->to_string(), p->to_string());
            continue;
          }
          auto r_neg = solver_->check_sat_assuming({smart_not(subst_p)});
          if (r_neg.is_unsat()) {
            predicates_to_use.push_back(subst_p);
            logger.log(1, "[extend_pred] related pred IMPLIED subst_p: {} (from {})", subst_p->to_string(), p->to_string());
          } else {
            logger.log(1, "[extend_pred] related pred NOT DETERMINED: {} (from {})", subst_p->to_string(), p->to_string());
          }
        } catch (const std::exception &) {
          continue;
        }
      }
      solver_->pop();
    }

    auto res = model_info_map_.emplace(cex, PerCexInfo(std::move(predicates_to_use)));
    model_info_pos = res.first;
  }

  auto preds = model_info_pos->second.preds_to_use;
  auto num_preds = preds.size();

  if (num_preds == 0) {
    auto t_end = std::chrono::steady_clock::now();
    total_extend_pred_time_ms += std::chrono::duration<double, std::milli>(t_end - t_start).count();
    total_extend_pred_calls++;
    return 0;
  }
  // conj_inout := VectorConcat(preds, conj_inout)
  preds.insert(preds.end(), conj_inout.begin(), conj_inout.end());
  conj_inout.swap(preds);

  // print all the predicates
  std::cout << "\n=== Extended Predicates Analysis ===\n";
  
  // Print variables in cex
  const auto & vars_in_cex = cex->get_varset_unslice();
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

  auto t_end = std::chrono::steady_clock::now();
  double elapsed_ms = std::chrono::duration<double, std::milli>(t_end - t_start).count();
  total_extend_pred_time_ms += elapsed_ms;
  total_extend_pred_calls++;
  logger.log(1, "[extend_pred] call #{}: {:.2f}ms (cumulative: {:.2f}ms)",
             total_extend_pred_calls, elapsed_ms, total_extend_pred_time_ms);

  return num_preds;
} // end of extend_predicates

} // namespace pono
