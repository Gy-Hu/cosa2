/*********************                                                        */
/*! \file
 ** \verbatim
 ** Top contributors (to current version):
 **   Ahmed Irfan, Makai Mann, Florian Lonsing
 ** This file is part of the pono project.
 ** Copyright (c) 2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **
 **
 **/

#include "engines/prover.h"

#include <cassert>
#include <climits>
#include <functional>
#include <fstream>

#include "core/rts.h"
#include "modifiers/static_coi.h"
#include "smt/available_solvers.h"
#include "utils/logger.h"
#include "utils/partial_model.h"
#include "frontends/property_if.h"

using namespace smt;
using namespace std;

namespace pono {

Prover::Prover(const Property & p,
               const TransitionSystem & ts,
               const smt::SmtSolver & s,
               PonoOptions opt)
    : initialized_(false),
      solver_(s),
      to_prover_solver_(s),
      orig_property_(p),
      orig_ts_(ts),
      ts_(ts, to_prover_solver_),
      unroller_(ts_),
      bad_(solver_->make_term(
          smt::PrimOp::Not,
          ts_.solver() == orig_property_.solver()
              ? orig_property_.prop()
              : to_prover_solver_.transfer_term(orig_property_.prop(), BOOL))),
      options_(opt),
      engine_(Engine::NONE)
{
}

Prover::~Prover() {}

void Prover::initialize()
{
  if (initialized_) {
    return;
  }

  reached_k_ = -1;

  if (!ts_.only_curr(bad_)) {
    throw PonoException("Property should not contain inputs or next state variables");
  }

  initialized_ = true;
}

ProverResult Prover::prove()
{
  return check_until(INT_MAX);
}

bool Prover::witness(std::vector<UnorderedTermMap> & out)
{
  if (!witness_.size()) {
    throw PonoException(
        "Recovering witness failed. Make sure that there was "
        "a counterexample and that the engine supports witness generation.");
  }

  function<Term(const Term &, SortKind)> transfer_to_prover_as;
  function<Term(const Term &, SortKind)> transfer_to_orig_ts_as;
  TermTranslator to_orig_ts_solver(orig_ts_.solver());
  if (solver_ == orig_ts_.solver()) {
    // don't need to transfer terms if the solvers are the same
    transfer_to_prover_as = [](const Term & t, SortKind sk) { return t; };
    transfer_to_orig_ts_as = [](const Term & t, SortKind sk) { return t; };
  } else {
    // need to add symbols to cache
    UnorderedTermMap & cache = to_orig_ts_solver.get_cache();
    for (const auto &v : orig_ts_.statevars()) {
      cache[to_prover_solver_.transfer_term(v)] = v;
    }
    for (const auto &v : orig_ts_.inputvars()) {
      cache[to_prover_solver_.transfer_term(v)] = v;
    }

    transfer_to_prover_as = [this](const Term & t, SortKind sk) {
      return to_prover_solver_.transfer_term(t, sk);
    };
    transfer_to_orig_ts_as = [&to_orig_ts_solver](const Term & t, SortKind sk) {
      return to_orig_ts_solver.transfer_term(t, sk);
    };
  }

  bool success = true;

  // Some backends don't support full witnesses
  // it will still populate state variables, but will return false instead of
  // true
  for (const auto & wit_map : witness_) {
    out.push_back(UnorderedTermMap());
    UnorderedTermMap & map = out.back();

    for (const auto &v : orig_ts_.statevars()) {
      const SortKind &sk = v->get_sort()->get_sort_kind();
      const Term &pv = transfer_to_prover_as(v, sk);
      map[v] = transfer_to_orig_ts_as(wit_map.at(pv), sk);
    }

    for (const auto &v : orig_ts_.inputvars()) {
      const SortKind &sk = v->get_sort()->get_sort_kind();
      const Term &pv = transfer_to_prover_as(v, sk);
      try {
        map[v] = transfer_to_orig_ts_as(wit_map.at(pv), sk);
      }
      catch (std::exception & e) {
        success = false;
        break;
      }
    }

    if (success) {
      for (const auto &elem : orig_ts_.named_terms()) {
        const SortKind &sk = elem.second->get_sort()->get_sort_kind();
        const Term &pt = transfer_to_prover_as(elem.second, sk);
        try {
          map[elem.second] = transfer_to_orig_ts_as(wit_map.at(pt), sk);
        }
        catch (std::exception & e) {
          success = false;
          break;
        }
      }
    }
  }

  return success;
}

size_t Prover::witness_length() const { return reached_k_ + 1; }

Term Prover::invar()
{
  if (!invar_)
  {
    throw PonoException("Failed to return invar. Be sure that the property was proven "
                        "by an engine the supports returning invariants.");
  }
  return to_orig_ts(invar_, BOOL);
}

Term Prover::to_orig_ts(Term t, SortKind sk)
{
  if (solver_ == orig_ts_.solver()) {
    // don't need to transfer terms if the solvers are the same
    return t;
  } else {
    // need to add symbols to cache
    TermTranslator to_orig_ts_solver(orig_ts_.solver());
    UnorderedTermMap & cache = to_orig_ts_solver.get_cache();
    for (const auto &v : orig_ts_.statevars()) {
      cache[to_prover_solver_.transfer_term(v)] = v;
      const Term &nv = orig_ts_.next(v);
      cache[to_prover_solver_.transfer_term(nv)] = v;
    }
    for (const auto &v : orig_ts_.inputvars()) {
      cache[to_prover_solver_.transfer_term(v)] = v;
    }
    // TODO: need a to add UFs to the cache also
    return to_orig_ts_solver.transfer_term(t, sk);
  }
}

Term Prover::to_orig_ts(Term t)
{
  return to_orig_ts(t, t->get_sort()->get_sort_kind());
}

bool Prover::compute_witness()
{
  // TODO: make sure the solver state is SAT
  if (options_.compute_dynamic_coi_upon_cex_) {
    smt::UnorderedTermSet varset;
    if (options_.use_ilang_coi_constraint_file_) {
      recursive_dynamic_COI_using_ILA_info(varset);
    } else {
      compute_dynamic_COI_from_term(bad_, reached_k_+1, varset);
    }
    std::ofstream fout("COI.txt");
    for (const auto & v : varset)
      fout << v->to_string() << std::endl;
  }

  for (int i = 0; i <= reached_k_ + 1; ++i) {
    witness_.push_back(UnorderedTermMap());
    UnorderedTermMap & map = witness_.back();

    for (const auto &v : ts_.statevars()) {
      const Term &vi = unroller_.at_time(v, i);
      const Term &r = solver_->get_value(vi);
      map[v] = r;
    }

    // early stop
    if (options_.witness_first_state_only_)
      return true;

    for (const auto &v : ts_.inputvars()) {
      const Term &vi = unroller_.at_time(v, i);
      const Term &r = solver_->get_value(vi);
      map[v] = r;
    }

    for (const auto &elem : ts_.named_terms()) {
      const Term &ti = unroller_.at_time(elem.second, i);
      map[elem.second] = solver_->get_value(ti);
    }
  }

  return true;
}


void Prover::get_var_in_COI(const TermVec & asts, UnorderedTermSet & vars) {
  PartialModelGen partial_model_getter(solver_);
  partial_model_getter.GetVarListForAsts(asts, vars);
}


void Prover::compute_dynamic_COI_from_term(const smt::Term & t, int k, smt::UnorderedTermSet & init_state_variables) {
  // bad_ ,  0...reached_k_+1
  // auto last_bad = unroller_.at_time(bad_, reached_k_+1);

  auto last_bad = unroller_.at_time(t, k);
  UnorderedTermSet varset;
  get_var_in_COI({last_bad}, varset); // varset contains variables like : a@n

  for(int i = reached_k_; i>=0; --i) {
    UnorderedTermSet newvarset;
    TermVec update_functions_to_check;
    for (const auto & var : varset) {
      auto untimed_var = unroller_.untime(var);  // a@n --> a

      if (ts_.is_input_var(untimed_var))
        continue;
      if (!ts_.is_curr_var(untimed_var)) // is_curr_var check if it is input var
        continue;
        
      auto pos = ts_.state_updates().find(untimed_var);

      if (pos == ts_.state_updates().end()) // this is likely
        continue; // because ts_ may promote input variables
      // therefore, there could be state vars without next function

      // assert(pos != ts_.state_updates().end());
      const auto & update_function = pos->second;  // a, b, c ...
      // at_time is used to change the variable set in update_function
      auto timed_update_function = unroller_.at_time(update_function, i); // i ?
      update_functions_to_check.push_back(timed_update_function);
    }
    get_var_in_COI(update_functions_to_check, newvarset);
  
    varset.swap(newvarset); // the same as "varset = newvarset;" , but this is faster
  }

  // varset at this point: a@0 ,  b@0 , ...
  for (const auto & timed_var : varset) { 
    init_state_variables.emplace(unroller_.untime(timed_var));
  }
} // end of compute_dynamic_COI_from_term


std::string static remove_vertical_bar(const std::string & in) {
  if (in.length() > 2 && in.front() == '|' && in.back() == '|')
    return in.substr(1,in.length()-2);
  return in;
}

void Prover::recursive_dynamic_COI_using_ILA_info(smt::UnorderedTermSet & init_state_variables) {

  AssumptionRelationReader IlaAsmptLoader("asmpt-ila.smt2", ts_);
  UnorderedTermSet init_sv;
  
  // initially, we extract bad
  set<std::pair<smt::Term, int>> next_round_to_track = { {bad_, reached_k_+1} };

  while(!next_round_to_track.empty()) {
    for (const auto & term_k_pair : next_round_to_track) {
      compute_dynamic_COI_from_term(term_k_pair.first, term_k_pair.second, init_sv);
    } // compute all sub var in 
    next_round_to_track.clear();

    // then let's go through all variables
    for (const auto & v : init_sv) {
      if (init_state_variables.find(v) != init_state_variables.end())
        continue; // to avoid repitition like v : v == another variable
      auto vname = remove_vertical_bar(v->to_string());
      if (IlaAsmptLoader.IsConstrainedInAssumption(vname)) {
        logger.log(0, "SV {} is in constraints", vname);
        auto cond = IlaAsmptLoader.GetConditionInAssumption(vname);
        auto val = IlaAsmptLoader.GetValueTermInAssumption(vname);

        for(int k = 0; k <= reached_k_+1; k++) {
          auto cond_at_k = unroller_.at_time(cond, k);
          auto is_cond_true_at_k = solver_->get_value(cond_at_k)->to_int();
          if(is_cond_true_at_k) {
            
            logger.log(0, "SV {} is triggered at Cycle #{}", vname, k);
            next_round_to_track.emplace(std::make_pair(val, k));
            break;
          }
        }
        logger.log(0, "WARNING: [COI] condition for {} was NOT triggered!", vname);
      } else {
        logger.log(0, "SV {} is NOT in constraints", vname);
        init_state_variables.emplace(v);
      }
    } // end for each init_sv
    
    logger.log(0, "----------------END of a round ----------------");
  } // end of while next_round_to_track is not empty

} // end of recursive_dynamic_COI_using_ILA_info

}  // namespace pono
