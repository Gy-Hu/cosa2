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
#include "core/fts.h"
#include<fstream> 
#include <cassert>
#include <climits>
#include <functional>
#include "json/json.hpp"
#include "core/rts.h"
#include "modifiers/static_coi.h"
#include "smt/available_solvers.h"
#include "utils/logger.h"
#include "utils/partial_model.h"

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
      // to_prover_solver_(create_solver_for(CVC5,
      //                               opt.engine_,
      //                               false,
      //                               opt.ceg_prophecy_arrays_)),
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
  // bool success = true;
  // if(options_.coi_filter_==true){
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
  // }
  // else{
  // auto new_solver = create_solver_for(BTOR, options_.engine_, true,false);
  // TermTranslator to_new_solver(new_solver);
  // // TermTranslator to_old_solver(solver_);
  // FunctionalTransitionSystem new_fts(ts_,to_new_solver);
  // UnorderedTermMap & cache = to_new_solver.get_cache();
  // for (const auto &v : orig_ts_.statevars()) {
  //   cache[to_new_solver.transfer_term(v)] = v;
  // }
  // for (const auto &v : orig_ts_.inputvars()) {
  //   cache[to_new_solver.transfer_term(v)] = v;
  // }
   
  // for (const auto & wit_map : witness_) {
  //   out.push_back(UnorderedTermMap());
  //   UnorderedTermMap & map = out.back();

  //   for (const auto &v : ts_.statevars()) {
  //     const SortKind &sk = v->get_sort()->get_sort_kind();
  //     const Term &pv = transfer_to_orig_as_(v, sk,new_solver);
  //     map[pv] = transfer_to_orig_as_(wit_map.at(v), sk,new_solver);
  //   }

  //   for (const auto &v : ts_.inputvars()) {
  //     const SortKind &sk = v->get_sort()->get_sort_kind();
  //     const Term &pv = transfer_to_orig_as_(v, sk,new_solver);
  //     try {
  //       map[pv] = transfer_to_orig_as_(wit_map.at(v), sk,new_solver);
  //     }
  //     catch (std::exception & e) {
  //       success = false;
  //       break;
  //     }
  //   }

  //   if (success) {
  //     for (const auto &elem : ts_.named_terms()) {
  //       const SortKind &sk = elem.second->get_sort()->get_sort_kind();
  //       const Term &pt = transfer_to_orig_as_(elem.second, sk,new_solver);
  //       try {
  //         map[pt] = transfer_to_orig_as_(wit_map.at(elem.second), sk,new_solver);
  //       }
  //       catch (std::exception & e) {
  //         success = false;
  //         break;
  //       }
  //     }
  //   }
  // }
  // }

  return success;
}

// Term Prover::transfer_to_orig_as_(const Term &t, const smt::SortKind &sk,TermTranslator to_new_solver){
//   return to_new_solver.transfer_term(t, sk);
// }

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
  if(options_.coi_filter_==true)
  {   
    smt::UnorderedTermMap varset;
    
    std::unordered_map <smt::Term,std::vector<pair<int,int>>> varset_slice;
    compute_dynamic_COI(varset,varset_slice);
    nlohmann::json j;
    // for(const auto v:varset){
    //   auto name = v->to_string();
    //   j["name"].push_back(name);
    // }
    auto btorsolver = create_solver(BTOR);
    auto transferer = smt::TermTranslator(btorsolver);
    std::string folderPath = options_.smt_path_;
    std::string filename = folderPath + "/" + "COI_variable.json";
    std::ofstream output(filename);    
    for(auto v = varset.begin(); v != varset.end(); v++) {
       std:: cout << v->first->to_string() << " : " << v->second->to_string() << std::endl;
       auto name = v->first->to_string();
       auto value_tansfer = transferer.transfer_term(v->second);
       j["name"].push_back(name);
       j["value"].push_back(value_tansfer->to_string());
    }
    for(auto v: varset_slice) {
       auto width = v.first->get_sort()->get_width();
       for(const auto width_pair: v.second){
          if((width_pair.first-width_pair.second+1)==width){
            std:: cout<< "The term: " << v.first->to_string()<< " cannot be extracted." << std::endl;
          }
          else{
            std:: cout<< "The extracted term is: " << v.first->to_string()<< " : " << width_pair.first<<" "<<width_pair.second << std::endl;
            j["name_to_extract"].push_back(v.first->to_string());
            j["extract_width"].push_back(width_pair);
          }
       }
    }

    output<<j<<std::endl;
  //   for (const auto & v : varset)
  //     std::cout << v->to_string() << std::endl;
  }
  for (int i = 0; i <= reached_k_ + 1; ++i) {
    witness_.push_back(UnorderedTermMap());
    UnorderedTermMap & map = witness_.back();
    auto new_solver = create_solver_for(BTOR, options_.engine_, false,false);
    auto transferer = smt::TermTranslator(new_solver);
    
    for (const auto &v : ts_.statevars()) {
      // auto new_v = transferer.transfer_term(v);
      const Term &vi = unroller_.at_time(v, i);
      const Term &r = solver_->get_value(vi);
      map[v] = r;
      // const Term &vi = unroller_.at_time(v, i);
      // const Term &r = solver_->get_value(vi);
      // auto new_v = transferer.transfer_term(vi);
      // auto new_r = transferer.transfer_term(r);
      // map[new_v] = new_r;
    }

    // early stop
    if (options_.witness_first_state_only_)
      return true;

    for (const auto &v : ts_.inputvars()) {
      // if(options_.coi_filter_==true){
      //   const Term &vi = unroller_.at_time(v, i);
      //   const Term &r = solver_->get_value(vi);
      //   map[v] = r;
      // }
      // else{
      const Term &vi = unroller_.at_time(v, i);
      const Term &r = solver_->get_value(vi);
      map[v] = r;
      // }
      // const Term &vi = unroller_.at_time(v, i);
      // const Term &r = solver_->get_value(vi);
      // // map[v] = r;
      // auto new_v = transferer.transfer_term(vi);
      // auto new_r = transferer.transfer_term(r);
      // map[new_v] = new_r;
    }

    for (const auto &elem : ts_.named_terms()) {
      const Term &ti = unroller_.at_time(elem.second, i);
      map[elem.second] = solver_->get_value(ti);
      // const Term &ti = unroller_.at_time(elem.second, i);
      // const Term &r = solver_->get_value(ti);
      // auto new_v = transferer.transfer_term(elem.second);
      // auto new_r = transferer.transfer_term(r);
      // map[new_v] = new_r;

    }
  }



  return true;
}




void Prover::get_var_in_COI(const std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> & input_asts, 
                                  std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> & varset_slice) {
  PartialModelGen partial_model_getter(solver_);
  partial_model_getter.GetVarListForAsts_in_bitlevel(input_asts, varset_slice);
}


void Prover::compute_dynamic_COI(UnorderedTermMap & init_state_variables, std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> & varset) {
  // bad_ ,  0...reached_k_+1
  // unroller_.change_solver(new_solver,new_ts_);
  // auto transferer = smt::TermTranslator(new_solver);
  // auto new_bad = transferer.transfer_term(bad_);
  auto last_bad = unroller_.at_time(bad_, reached_k_+1);
  // std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> varset;

  get_var_in_COI({{last_bad,{{0,0}}}}, varset); // varset contains variables like : a@n
  // for(auto var:ts_.inputvars()){
  //   std::cout<<"The input var is: "<<var->to_string()<<std::endl;
  // }
  for(int i = reached_k_; i>=0; --i) {
    std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> update_functions_to_check;
    std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> newvarset_slice;
    for (const auto & var_ranges_pair : varset) { // for each variable in varset, trace back to the update functions
      auto untimed_var = unroller_.untime_var(var_ranges_pair.first);  // a@n --> a

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
      // get_input_var_in_COI(update_functions_to_check,varset_input);
      auto timed_update_function = unroller_.at_time(update_function, i); // i ?
      update_functions_to_check.emplace(timed_update_function, var_ranges_pair.second);
    } // for each variable in varset
    
    get_var_in_COI(update_functions_to_check, newvarset_slice);
    
  
    varset.swap(newvarset_slice); // the same as "varset = newvarset;" , but this is faster
  }

  // varset at this point: a@0 ,  b@0 , ...
  for (const auto & timed_var : varset) { 
    init_state_variables[unroller_.untime_var(timed_var.first)] = solver_->get_value(timed_var.first);
  }
}

}  // namespace pono
