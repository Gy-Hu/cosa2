/*********************                                                        */
/*! \file 
 ** \verbatim
 ** Top contributors (to current version):
 **   Hongce Zhang
 ** This file is part of the cosa2 project.
 ** Copyright (c) 2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The SAT-based Enumerator with Policy
 **
 ** 
 **/

#include "policy_sat_enum.h"
#include "utils/multitimer.h"
#include "utils/term_analysis.h"
#include "utils/str_util.h"
#include "utils/container_shortcut.h"
#include "utils/logger.h"

#include "engines/apdr/config.h"
#include <cassert>
#include <cmath>

// some helper functions
#define TERM_TRUE    (solver_->make_term(true))
#define NOT(x)       (solver_->make_term(smt::Not, (x)))
#define NOT_msat(x)  (msat_solver_->make_term(smt::Not, (x)))
#define EQ(x, y)     (solver_->make_term(smt::Equal, (x), (y)))
#define AND(x, y)    (solver_->make_term(smt::And, (x), (y)))
#define OR(x, y)     (solver_->make_term(smt::Or, (x), (y)))
#define IMPLY(x, y)  (solver_->make_term(smt::Implies, (x), (y)))
#define IFF(x, y)    (solver_->make_term(smt::Iff, (x), (y)))

//#define DEBUG
#ifdef DEBUG
  #define D(...) logger.log( __VA_ARGS__ )
  #define INFO(...) D(0, __VA_ARGS__)
#else
  #define D(...) do {} while (0)
  #define INFO(...) logger.log(1, __VA_ARGS__)
#endif

#define TERM_TABLE_DEBUG_LVL 1

namespace cosa {

namespace policy_sat_enum {

// --------------------  eval_val ----------------

eval_val::eval_val(const std::string & val) {
  assert(val.find("#b") == 0);
  size_t pos = 2;
  for(; pos < val.length() ; ++ pos) {
    if ( val.at(pos) != '0' )
      break;
  }
  if (pos == val.length()) {
    // result 0
    type = type_t::NUM;
    nv = 0;
  } else {
    try {
      nv = sygus::StrToULongLong(val.substr(pos), 2);
      type = type_t::NUM;      
    } catch (...) {
      type = type_t::STR;
      sv = val.substr(pos);
    }
  }
} // eval_val::eval_val

bool eval_val::operator<(const eval_val &r) const {
  if (type == type_t::NUM && r.type == type_t::STR)
    return true;
  if (type == type_t::STR && r.type == type_t::NUM)
    return false;
  if (type == type_t::NUM)
    return nv < r.nv;
  // both str
  if (sv.length() < r.sv.length())
    return true;
  if (sv.length() > r.sv.length())
    return false;
  for(size_t pos = 0; pos < sv.length(); ++ pos) {
    if (sv.at(pos) == '0' && r.sv.at(pos) == '1')
      return true;
    if (sv.at(pos) == '1' && r.sv.at(pos) == '0')
      return false;
  }
  return false; // equal both string, same length and save val
}

// --------------------  enum_status ----------------
bool enum_status::is_uninit() const {
  return ( curr_predicate_num == 0 );
}

void enum_status::init() {
  assert( is_uninit() );
  increase_predicate_num();
} // init

z3::expr enum_status::and_of_predvs(const std::unordered_set<size_t> & pred_idxs) {
  auto c = sat_context_.bool_val(true);
  for (auto idx : pred_idxs)
    c = c && pred_v_.at(idx);
  return c;
}

z3::expr enum_status::or_of_predvs(const std::unordered_set<size_t> & pred_idxs) {
  auto c = sat_context_.bool_val(false);
  for (auto idx : pred_idxs)
    c = c || pred_v_.at(idx);
  return c;
}

z3::expr enum_status::and_of_all_predvs() {
  auto c = sat_context_.bool_val(true);
  for (z3::expr & p : pred_v_)
    c = c && p;
  return c;
}

z3::expr enum_status::or_of_all_predvs() {
  auto c = sat_context_.bool_val(false);
  for (z3::expr & p : pred_v_)
    c = c || p;
  return c;
}

// pre, post -> true/false

void enum_status::increase_predicate_num() {
  assert(predicate_list_btor.size() == predicate_list_msat.size());
  assert(predicate_list_btor.size() == predicate_list_btor_next.size());
  assert(predicate_list_btor.size() > curr_predicate_num);

  // TODO: we need to create vars and clear things here !!!
  auto old_size = curr_predicate_num;
  auto new_size = predicate_list_btor.size();
  // create vars
  assert(pred_v_.size() == old_size);
  // std::unordered_set<size_t> new_pred_idxs;
  z3::expr or_of_new_preds = sat_context_.bool_val(false);
  for (size_t idx = old_size; idx < new_size; ++ idx) {
    std::string n = ( "p"+ std::to_string(idx) );
    z3::expr p = sat_context_.bool_const(n.c_str());
    pred_v_.push_back(p);
    or_of_new_preds = or_of_new_preds || p;
    // update num_of_true_pred_
    num_of_true_pred_ = num_of_true_pred_ + z3::ite(p, one, zero);
  }
  // 
  sat_solver_.reset();
  sat_solver_.add(or_of_all_predvs());
  // augument the old one with new possibilities
  for (auto & impl_expr : existing_impls_) {
    // insert new_pred_idxs into impl_rel;
    impl_expr = impl_expr || or_of_new_preds;
    sat_solver_.add(impl_expr);
  }

  // final updates
  curr_predicate_num = predicate_list_btor.size();
  true_preds_.clear();
} // increase_predicate_num


void enum_status::dump() const {  
  // print imps_
#ifdef DEBUG
  for(auto && rel: existing_impls_) {
    std::cout << rel << std::endl;
  }
#endif
  // print current preds
  if (true_preds_.empty())
    std::cout <<"()";
  for(auto pred : true_preds_)
    std::cout << pred<<",";
  std::cout <<" , # preds : "<< curr_predicate_num << "*" << curr_conjunction_depth <<std::endl;
}

smt::Term enum_status::GetCandidateBtor(smt::SmtSolver & solver_) const {
  assert (!true_preds_.empty());
  smt::Term ret = nullptr;
  for (auto idx : true_preds_ ) {
    assert(idx < predicate_list_btor.size());
    if (ret == nullptr)
      ret = predicate_list_btor.at(idx);
    else
      ret = AND(ret, predicate_list_btor.at(idx));
  }
  return ret;
}


smt::Term enum_status::GetCandidateBtorNext(smt::SmtSolver & solver_) const {
  assert (!true_preds_.empty());
  smt::Term ret = nullptr;
  for (auto idx : true_preds_ ) {
    assert(idx < predicate_list_btor_next.size());
    if (ret == nullptr)
      ret = predicate_list_btor_next.at(idx);
    else
      ret = AND(ret, predicate_list_btor_next.at(idx));
  }
  return ret;
}

smt::Term enum_status::GetCandidateMsat(smt::SmtSolver & solver_) const {
  assert (!true_preds_.empty());
  smt::Term ret = nullptr;
  for (auto idx : true_preds_ ) {
    assert(idx < predicate_list_msat.size());
    if (ret == nullptr)
      ret = predicate_list_msat.at(idx);
    else
      ret = AND(ret, predicate_list_msat.at(idx));
  }
  return ret;
}

// usually called with new_impl(curr_true_pred(), {set of pred that are needed or none})
// or if their disj becomes top
void enum_status::new_impl(const std::unordered_set<size_t> & pre, const std::unordered_set<size_t> & post) {
  z3::expr impl_rel = z3::implies( and_of_predvs(pre) , or_of_predvs(post) );
  existing_impls_.push_back(impl_rel);
  sat_solver_.add(impl_rel);
}


// if give 0, then will try to find only that much
bool enum_status::next_pred_assignment(size_t conjunction_depth) { // return false if unsat --> no pred under the current pred num
  true_preds_.clear();
  if (conjunction_depth != 0) {
    sat_solver_.push();
    sat_solver_.add(num_of_true_pred_ <= sat_context_.int_val(conjunction_depth) );
  }
  GlobalTimer.RegisterEventStart("Enum.Z3Query",0);
  auto psat = sat_solver_.check();
  GlobalTimer.RegisterEventEnd("Enum.Z3Query",1);

  if (psat == z3::check_result::sat) {
    auto m = sat_solver_.get_model();
    for (size_t pidx = 0; pidx < pred_v_.size() ; ++ pidx) {
      const z3::expr & p = pred_v_.at(pidx);
      try {
        if( m.eval(p, false).is_true() )
          true_preds_.insert(pidx);
      } catch (...) {
        // its value is not assigned
        // therefore not matter
      }
    } // for each pred
    assert (!true_preds_.empty()); // there must be some that are assigned
    if(conjunction_depth != 0) {
      sat_solver_.pop();
      assert(true_preds_.size() <= conjunction_depth);
    }

    #ifdef DEBUG
    std::cout << "[sat-enum]: ";
    for(auto pidx : true_preds_)
      std::cout << pidx << " ";
    std::cout << std::endl;
    #endif

    return true;
  } // end of extraction of model
  if(conjunction_depth != 0)
    sat_solver_.pop();
  
  D(1, "[sat-enum]: no candidate");

  return false; // unsat // no pred will work
} // next_pred_assignment


// ----------------------------------------------------------------
//
//                         Term Table
//
//                       Member Functions
//
// ----------------------------------------------------------------

#define IS_LE(x) \
  ((x) == term_policy_action_t::ITP_V_C_CMP_LE || \
   (x) == term_policy_action_t::V_C_CMP_LE || \
   (x) == term_policy_action_t::V_C_OP_CMP_LE || \
   (x) == term_policy_action_t::TERM_3_CMP_LE || \
   (x) == term_policy_action_t::ITP_V_C_OP_CMP_LE) 

#define IS_LT(x) \
  ((x) == term_policy_action_t::ITP_V_C_CMP_LT || \
   (x) == term_policy_action_t::V_C_CMP_LT || \
   (x) == term_policy_action_t::V_C_OP_CMP_LT || \
   (x) == term_policy_action_t::TERM_3_CMP_LT || \
   (x) == term_policy_action_t::ITP_V_C_OP_CMP_LT) 

#define IS_EQ(x) \
  ((x) == term_policy_action_t::ITP_V_C_EQ || \
   (x) == term_policy_action_t::V_C_EQ || \
   (x) == term_policy_action_t::V_C_OP_EQ || \
   (x) == term_policy_action_t::TERM_3_EQ || \
   (x) == term_policy_action_t::ITP_V_C_OP_EQ) 


void term_table_t::set_all_comp_pointers(uint64_t ptr) {
  if ( IS_LE(term_policy_action) ) {
      prev_eq_pointer = prev_comp_lt_pointer = prev_comp_le_pointer = ptr;
  } else if ( IS_LT(term_policy_action)  ) {
    prev_eq_pointer = prev_comp_lt_pointer = ptr;
  } else {
    prev_eq_pointer = ptr;
  }
}

void term_table_t::reset(term_policy_action_t action) {
  terms.clear();
  terms_val_under_cex.clear();
  // term_strings will not clear
  n_vars = n_consts_vars = prev_unary_pointer = prev_binary_pointer =
    prev_ternary_pointer_same_width = prev_ternary_pointer_bool = 
    prev_eq_pointer = prev_comp_lt_pointer = prev_comp_le_pointer = 0;

  term_policy_action = action;
}

std::tuple<bool, bool, bool> term_table_t::reg_comp_idxs(size_t idx1, size_t idx2, uint64_t width) {
  bool has_le = false, has_lt = false, has_eq = false;
  if ( IS_LE(term_policy_action) ) 
    has_le = has_lt = has_eq = true;
  else if ( IS_LT(term_policy_action) )
    has_lt = has_eq = true;
  else
    has_eq = true;

  if (has_le)
    has_le = !(idx1 < prev_comp_le_pointer && idx2 < prev_comp_le_pointer);

  if (has_lt) 
    has_lt = !(idx1 < prev_comp_lt_pointer && idx2 < prev_comp_lt_pointer);

  if (has_eq)
    has_eq = !(idx1 < prev_eq_pointer && idx2 < prev_eq_pointer);
  
  return std::make_tuple(has_le, has_lt, has_eq);
}

#undef IS_LE
#undef IS_LT
#undef IS_EQ


// ----------------------------------------------------------------
//
//                         Enumerator
//
//                       Helper Functions
//
// ----------------------------------------------------------------

Enumerator::prop_pos_buf_t Enumerator::prop_enum_buf_;
Enumerator::cex_pos_buf_t  Enumerator::cex_enum_buf_;

Enumerator::prop_term_map_t Enumerator::prop_term_map_;
Enumerator::cex_term_map_t  Enumerator::cex_term_map_;

void Enumerator::ClearCache() {
  prop_enum_buf_.clear();
  cex_enum_buf_.clear();
  prop_term_map_.clear();
  cex_term_map_.clear();
}


bool Enumerator::is_valid(const smt::Term & e) {
  solver_->push();
  solver_->assert_formula(NOT(e));
  auto result = solver_->check_sat();
  solver_->pop();
  return !(result.is_sat());
}
  
bool Enumerator::a_implies_b(const smt::Term & a, const smt::Term & b) {
  return is_valid(IMPLY(a,b));
}


bool Enumerator::is_predicate_const(const smt::Term & t) {
  //auto term_string = t->to_raw_string();
  {
    //std::cout << "[is_predicate_const] Checking " << term_string << std::endl;
    solver_->push();
      solver_->assert_formula(t);
      auto r = solver_->check_sat();
    solver_->pop();
    if (r.is_unsat()) // is always false
      return true;
  }
  {
    // std::cout << "[is_predicate_const] Checking NOT( " << term_string <<")" << std::endl;
    solver_->push();
      solver_->assert_formula(NOT(t));
      auto r = solver_->check_sat();
    solver_->pop();
    if (r.is_unsat()) // is always true
      return true;
  }
  return false;
} // is_predicate_const

bool Enumerator::is_predicate_implicable(const smt::Term & t) {
  if(use_cex_) {
    // cex should imply this
    auto cex_p = cexs_[0]->to_expr_btor(solver_);
    solver_->push();
      solver_->assert_formula(cex_p); // cex_p , but not t
      solver_->assert_formula(NOT(t)); //
      auto r = solver_->check_sat();
    solver_->pop();
    if (r.is_sat())
      return false;
    return true;
  } // else not using use_cex_
    solver_->push();
      solver_->assert_formula(NOT(prop_)); // cex_p , but not t
      solver_->assert_formula(NOT(t)); //
      auto r = solver_->check_sat();
    solver_->pop();
    if (r.is_sat())
      return false;
    return true;
} // is_predicate_implicable

bool Enumerator::init_imply(const smt::Term & c) {
  solver_->push();
    solver_->assert_formula(init_);
    D(0, "[init_imply] assert {} ", init_->to_string());
    solver_->assert_formula(NOT(c));
    D(0, "[init_imply] assert not({}) ", c->to_string());
    auto r = solver_->check_sat();
    if (r.is_sat()) {
      // now we are going to iterate along those pred
      // and find whose value under this model is 1 
      // and then we must select from among them
#ifdef DEBUG
      { // dumping state assignments
        smt::UnorderedTermSet all_symbols;
        get_free_symbols(init_, all_symbols);
        get_free_symbols(c, all_symbols);
        for (const auto & s : all_symbols) {
          std::cout << "[init_imply] " << s->to_string() << " = " << solver_->get_value(s)->to_string() << std::endl;
        }
      }
#endif
      std::unordered_set<size_t> post_or; 
      for(size_t pidx = 0; pidx < predicate_list_btor_.size(); ++ pidx) {
        // evaluate those preds
        const auto & p = predicate_list_btor_.at(pidx);
        if ( solver_->get_value(NOT(p))->to_int() != 0ULL ) {
          post_or.insert(pidx);
          assert(!IN(pidx, enum_status_.curr_true_pred()));
        }
      } // for each pred
      enum_status_.new_impl(enum_status_.curr_true_pred(), post_or);

    }
  solver_->pop();
  return !(r.is_sat());
} // init_imply

bool Enumerator::compatible_w_facts(const smt::Term & c) {
  if(facts_.empty()) // shortcut
    return true;
  
  size_t fact_idx = 0;
  std::unordered_set<size_t> incompatible_fact_idxs;
  solver_->push();
    solver_->assert_formula(c);
    std::cout << "facts size : " << facts_.size() << std::endl;
    for (auto f_ptr : facts_) {
      solver_->push();
      std::cout << "F : " << f_ptr->to_string() << std::endl;
      solver_->assert_formula(f_ptr->to_expr_btor(solver_));
      bool compatible = solver_->check_sat().is_sat();
      solver_->pop();
      
      if(!compatible)
        incompatible_fact_idxs.insert(fact_idx);

      ++ fact_idx;
    }
  solver_->pop();

  // add new lemmas
  for (auto fidx : incompatible_fact_idxs) {
    Model * f_ptr = facts_.at(fidx);
    solver_->push();
    solver_->assert_formula(f_ptr->to_expr_btor(solver_));
    bool sat = solver_->check_sat().is_sat();
    assert (sat);
    std::unordered_set<size_t> post_or;
    for(size_t pidx = 0; pidx < predicate_list_btor_.size(); ++ pidx) {
      // evaluate those preds
      const auto & p = predicate_list_btor_.at(pidx);
      if ( solver_->get_value(NOT(p))->to_int() != 0ULL ) {
        post_or.insert(pidx);
        assert(!IN(pidx, enum_status_.curr_true_pred()));
      }
    }
    solver_->pop();
    enum_status_.new_impl(enum_status_.curr_true_pred(), post_or);
  }

  return incompatible_fact_idxs.empty();
} // compatible_w_facts

bool Enumerator::F_T_and_P_imply_Pprime(const smt::Term & c, const smt::Term & c_nxt) {
  solver_->push();
    solver_->assert_formula(prev_);
    solver_->assert_formula(c);
    solver_->assert_formula(trans_);
    solver_->assert_formula(NOT(c_nxt));
    auto r = solver_->check_sat();
    if (r.is_sat()) {
      // now we are going to iterate along those pred
      // and find whose value under this model is 1 
      // and then we must select from among them
      #ifdef DEBUG
      // std::cout << "Eval: ";
      for (auto && w_t_pair : width_term_table_) {
        auto width = w_t_pair.first;
        const auto & terms = w_t_pair.second;
        for (auto vidx = 0; vidx < terms.n_vars; ++ vidx) {
          auto v = terms.terms.at(vidx).first;
          std::cout << v->to_string() << ":=" << solver_->get_value(v)->to_string() << " , ";
          auto v_nxt = to_next_(terms.terms.at(vidx).first);
          std::cout << v_nxt->to_string() << ":=" << solver_->get_value(v_nxt)->to_string() << " , ";
        }
      }
      std::cout << "END\n";
      #endif

      std::unordered_set<size_t> post_or; 
      for(size_t pidx = 0; pidx < predicate_list_btor_.size(); ++ pidx) {
        // evaluate those preds
        const auto & p = predicate_list_btor_next_.at(pidx);
        auto val =  solver_->get_value(NOT(p))->to_int();
        D(0, "[F_T_and_P] eval NOT({}) on s' , get {} ", p->to_string() ,  val);
        if ( val != 0ULL ) {
          post_or.insert(pidx);
          assert(!IN(pidx, enum_status_.curr_true_pred()));
        }
      } // for each pred // QUESTION: temp impl? unless F is F0
      enum_status_.new_impl(enum_status_.curr_true_pred(), post_or);
    } // if not valid
  solver_->pop();
  return !(r.is_sat());
} // F_T_and_P_imply_Pprime


void Enumerator::insert_comp(smt::PrimOp smt_op, const btor_msat_term_pair_t & l, const btor_msat_term_pair_t & r) {
  auto pred_btor = solver_->make_term(smt::Op(smt_op), l.first, r.first);
  auto pred_syntactic_hash = pred_btor->to_raw_string();
  if (IN(pred_syntactic_hash, predicate_set_btor_))
    return; // duplicated predicates -- avoid
  if (is_predicate_const(pred_btor))
    return; // do nothing
  auto pred_msat = msat_solver_->make_term(smt::Op(smt_op), l.second, r.second);
  predicate_list_btor_.push_back(pred_btor);
  predicate_list_btor_next_.push_back(to_next_(pred_btor));
  predicate_list_msat_.push_back(pred_msat);
  predicate_set_btor_.insert(pred_syntactic_hash);
} // Enumerator::insert_comp


// ----------------------------------------------------------------
//
//                         Enumerator
//
//                        Main Functions
//
// ----------------------------------------------------------------


Enumerator::Enumerator(
    btor_var_to_msat_t btor_var_to_msat_func,
    to_next_t to_next_func,
    smt::SmtSolver & btor_solver,
    smt::SmtSolver & msat_solver,
    const smt::Term & T_btor, const smt::Term & Init_btor, const smt::Term & Fprev_btor,
    const std::vector<Model *> & cexs, const std::vector<Model *> & facts,
    const smt::Term & prop_btor,
    const sygus::SyntaxStructure & syntax,
    const ApdrSygusHelper & itp_info ):
      btor_var_to_msat_(btor_var_to_msat_func),
      to_next_(to_next_func),
      solver_(btor_solver), msat_solver_(msat_solver),
      trans_(T_btor), init_(Init_btor), prev_(Fprev_btor),
      cexs_(cexs), facts_(facts), prop_(prop_btor),
      syntax_(syntax), syntax_struct_(syntax.GetSyntaxConstruct()),
      itp_info_(itp_info),
      use_cex_(!cexs.empty()),
      width_term_table_(SetupInitTermList()),
      enum_status_(SetUpEnumStatus()),
      curr_conjunction_depth(enum_status_.curr_conjunction_depth),
      predicate_list_btor_(enum_status_.predicate_list_btor),
      predicate_list_btor_next_(enum_status_.predicate_list_btor_next),
      predicate_list_msat_(enum_status_.predicate_list_msat),
      predicate_set_btor_(enum_status_.predicate_set_btor)
{
  // SetupInitialPredicateListAndEnumStatus
  // term table dump

  if (enum_status_.is_uninit())
    enum_status_.init(); // set initial predicate num
}


enum_status & Enumerator::SetUpEnumStatus() {
  if(use_cex_) {
    assert(cexs_.size() == 1);
    Model * cex = cexs_.at(0);
    return cex_enum_buf_[cex];
    // will create, but need to take care of the size of curr_s anyway
  }
  else {
    return prop_enum_buf_[prop_];
  }
  assert (false); // should not be reachable
} // Enumerator::SetUpEnumStatus()

Enumerator::width_term_table_t & Enumerator::SetupInitTermList() {
  width_term_table_t * w2symbols_ptr;
  if(use_cex_) {
    assert(cexs_.size() == 1);
    Model * cex = cexs_.at(0);
    auto pos = cex_term_map_.find(cex);
    if (pos != cex_term_map_.end())
      return pos->second;
    // now create the index
    w2symbols_ptr = &cex_term_map_[cex];
    PopulateTermTableWithSyntaxVars(*w2symbols_ptr);
    // estimate the numbers here
  } else {
    auto pos = prop_term_map_.find(prop_);
    if (pos != prop_term_map_.end())
      return pos->second;

    w2symbols_ptr = &prop_term_map_[prop_]; // will create
    PopulateTermTableWithSyntaxVars(*w2symbols_ptr);
  }

  PopulateTermTableWithConstants(*w2symbols_ptr);

#if TERM_TABLE_DEBUG_LVL == 1
  // a light weight dump function
  PrintWidthTermTableSimple(width_term_table_);
#endif
#if TERM_TABLE_DEBUG_LVL == 2
  PrintWidthTermTable(width_term_table_);
#endif

  for (auto & w_term_pair : *w2symbols_ptr) {
    auto npred = term_estimator:: estimate_predicate_num_for_V_C( 
      w_term_pair.second.n_vars /*nV*/ ,
      w_term_pair.second.n_consts_vars - w_term_pair.second.n_vars  /*nC*/ );
    if (npred > GlobalAPdrConfig.SYGUS_PREDICATE_EFFORTS) {
      w_term_pair.second.term_policy_action = term_policy_action_t::ITP_V_C_EQ;
      ReplaceTermWithItpVC(w_term_pair.first, w_term_pair.second);
    } else {
      w_term_pair.second.term_policy_action = term_policy_action_t::V_C_EQ;
    }
    // init policy for predicates
    
    PopulatePredicateListsWithTermsIncr(w_term_pair.first, w_term_pair.second, 0, 0); // default start end (all)
  }

  return *w2symbols_ptr;
} // SetupInitTermList

// Member used: use_cex_, cexs_, prop_
// Update parameter: table
void Enumerator::PopulateTermTableWithSyntaxVars(width_term_table_t & table) const {
  if(use_cex_) {
    assert(cexs_.size() == 1);
    Model * cex = cexs_.at(0);
    // now collect symbols
    for (auto && v_val : cex->cube ) {
      const auto & v = v_val.first;
      assert ( v->is_symbolic_const() );
      uint64_t width = sygus::get_width_of_var(v);
      table[width].terms.push_back(std::make_pair(v, btor_var_to_msat_(v)));
    }
  } else {
    smt::UnorderedTermSet all_symbols;
    get_free_symbols(prop_, all_symbols);

    for (auto && v : all_symbols) {
      uint64_t width = sygus::get_width_of_var(v);
      table[width].terms.push_back(std::make_pair(v, btor_var_to_msat_(v))); // will create
    }
  } // end of cex/prop
  for (auto & w_term_pair : table)
    w_term_pair.second.n_vars = w_term_pair.second.terms.size();
} // end of PopulateTermTableWithSyntaxVars


 //  initial population of tables 
void Enumerator::PopulateTermTableWithConstants(width_term_table_t & table) const {
  // width -> vars and constants and then apply comps on them
  // output: predicate_list_btor_, predicate_list_btor_next_, predicate_list_msat_

  // SetupInitTermList already set up vars
  // add constants from grammar
  std::unordered_set<std::string> bool_consts = {"true", "false"};
  std::unordered_set<std::string> bv1_consts = {"#b0", "#b1"};
  // you can add more enumeration if wanted

  for (const auto & w_syntax : syntax_struct_ ) {
    uint64_t width = w_syntax.first;
    const auto & syntax = w_syntax.second;
    const std::unordered_set<std::string> & cnsts_set
      = (width == 0) ? bool_consts : (
        (width == 1) ? bv1_consts  : (
        syntax.constants));
      
    for (const auto & c: cnsts_set) {
      table[width].terms.push_back(std::make_pair(
        sygus::smt_string_to_const_term(c, solver_),
        sygus::smt_string_to_const_term(c, msat_solver_)
        ));
      table[width].term_strings.insert(
        table[width].terms.back().first->to_raw_string());
    }
  }

  for (auto & w_term_pair : table)
    w_term_pair.second.n_consts_vars = w_term_pair.second.terms.size();
} // Enumerator::SetupInitialTermTable

void Enumerator::PopulateTermTableWithUnaryOp(uint64_t width, term_table_t & terms, uint64_t start, uint64_t end) {

  auto syntax_pos = syntax_struct_.find(width);
  if (syntax_pos == syntax_struct_.end())
    return;
  const auto & op_unary = syntax_pos->second.op_unary;
  if (op_unary.empty())
    return;
  
  if (start == 0)
    start = terms.prev_binary_pointer;
  if (end == 0)
    end = terms.terms.size();

  assert (start <= end && end <= terms.terms.size());
  if (start < terms.prev_unary_pointer)
    D(1, "[Warning] Repeated unary op enumerated");

  if(terms.n_vars == 0 && terms.terms.size() == terms.n_consts_vars) {
    // no vars and no extra terms
    terms.prev_unary_pointer = terms.terms.size();
    return; // no vars captured for this, and no other terms to work on
  }

  for (auto && op: op_unary) {
    auto smt_op = smt::Op(op);
    for(auto idx = start; idx < end; ++ idx) {
      auto btor_new_term = solver_->make_term(smt_op, terms.terms.at(idx).first);
      //if (btor_new_term->is_value()) {
      if (btor_new_term->is_symbolic_const())
        continue;
      // for op & value, let's do the check
      auto v = btor_new_term->to_raw_string();
      if (terms.term_strings.find(v) != terms.term_strings.end())
        continue; // skip this
      terms.term_strings.insert(v);

      terms.terms.push_back(
        std::make_pair(
          btor_new_term, // btor_term
          msat_solver_->make_term(smt_op, terms.terms.at(idx).second) // msat_term
      ));
    }
  } // end for each op
  if (end < terms.prev_unary_pointer )
    D(1, "[Warning] Unary op enumeration is unwinded");
  terms.prev_unary_pointer = end;

} // PopulateTermTableWithUnaryOp


void Enumerator::PopulateTermTableWithBinaryOp(uint64_t width, term_table_t & terms, uint64_t start, uint64_t end) {

  auto syntax_pos = syntax_struct_.find(width);
  if (syntax_pos == syntax_struct_.end())
    return;
  const auto & op_binary = syntax_pos->second.op_binary;
  if (op_binary.empty())
    return;
  
  if (start == 0)
    start = terms.prev_binary_pointer;
  if (end == 0)
    end = terms.terms.size();

  assert (start <= end && end <= terms.terms.size());
  if (start < terms.prev_binary_pointer)
    D(1, "[Warning] Repeated binary op enumerated");

  if(terms.n_vars == 0 && terms.terms.size() == terms.n_consts_vars) {
    // no vars and no extra terms
    terms.prev_binary_pointer = terms.terms.size();
    return; // no vars captured for this, and no other terms to work on
  }

  auto prev_pos = start;
  for (auto && op: op_binary) {
    auto smt_op = smt::Op(op);
    bool symmetry = sygus::is_primop_symmetry(op);
    for(auto idx1 = 0; idx1 < end; ++ idx1) { // a-b and b-a
      for(auto idx2 = ( idx1 < prev_pos ? prev_pos : 
          (symmetry ? idx1 : 0)) ; 
        idx2 < end; ++ idx2) {
        assert(!( idx1 < prev_pos && idx2 < prev_pos )); // no repetition
        auto btor_new_term = solver_->make_term(smt_op, terms.terms.at(idx1).first, terms.terms.at(idx2).first);

        if (btor_new_term->is_symbolic_const())
          continue; // will not add vars

        auto v = btor_new_term->to_raw_string();
        if (terms.term_strings.find(v) != terms.term_strings.end())
          continue; // skip this
        terms.term_strings.insert(v);

        terms.terms.push_back(  
        std::make_pair(
          btor_new_term,
          msat_solver_->make_term(smt_op, terms.terms.at(idx1).second, terms.terms.at(idx2).second)));
      } // for idx2
    } // for idx1
  } // for each op
  if (end < terms.prev_binary_pointer )
    D(1, "[Warning] Binary op enumeration is unwinded");
  terms.prev_binary_pointer = end;

} // PopulateTermTableWithBinaryOp



// terms to predicates
void Enumerator::PopulatePredicateListsWithTermsIncr(uint64_t width, term_table_t & terms, uint64_t start, uint64_t end) {
  assert (predicate_list_btor_.size() == predicate_list_msat_.size());
  assert (predicate_list_btor_.size() == predicate_list_btor_next_.size());

  // for each width, depends on the status, decide which pointer to use

  GlobalTimer.RegisterEventStart("Enum.PredicateGen", predicate_list_btor_.size());

    auto nterms = end == 0 ? terms.terms.size() : end;

    if(terms.n_vars == 0 && (nterms - terms.n_consts_vars == 0) ) {
      terms.set_all_comp_pointers(nterms);
      return; // skip those without vars;
    }
    // interprete the variables based on the cex/prop
    // so that, based on values, you can decide what comparator to use
    if (terms.terms.size() > terms.terms_val_under_cex.size()) {
      // assert that in the solver
      solver_->push();
      if(use_cex_) {
        auto cex_p = cexs_.at(0)->to_expr_btor(solver_);
        solver_->assert_formula(cex_p);
      } else
        solver_->assert_formula(NOT(prop_));
      auto r = solver_->check_sat();
      assert(r.is_sat());
      for (size_t idx = terms.terms_val_under_cex.size() ; 
          idx < terms.terms.size(); ++ idx) {
        terms.terms_val_under_cex.push_back(eval_val(
          solver_->get_value(terms.terms.at(idx).first)->to_raw_string()));
      }
      solver_->pop();
    } // finish eval new terms

    for (size_t idx1 = 0; idx1 < nterms; ++idx1 ) { // will end at "end" if end != 0
      for (size_t idx2 = idx1+1 ; idx2 < nterms; ++ idx2) {
        if (idx1 < start && idx2 < start) // only if start > 0, this will work
          continue;

        auto [has_le, has_lt, has_eq] = terms.reg_comp_idxs(idx1, idx2, width);
        if (! has_le && !has_lt && !has_eq)
          continue;

        // if (idx1 < skip_pos && idx2 < skip_pos)
        //  continue;
        // get the values and decide what to do
        const auto & v1 = terms.terms_val_under_cex.at(idx1);
        const auto & v2 = terms.terms_val_under_cex.at(idx2);
        if (!(v1 == v2)) {
          if (has_lt) {
            if (v1 < v2)
              insert_comp(smt::PrimOp::BVUlt, terms.terms.at(idx1), terms.terms.at(idx2));
            else // v2 < v1
              insert_comp(smt::PrimOp::BVUlt, terms.terms.at(idx2), terms.terms.at(idx1));
          } // has lt
          if (has_le) {
            if (v1 < v2)
              insert_comp(smt::PrimOp::BVUle, terms.terms.at(idx1), terms.terms.at(idx2));
            else // v2 < v1
              insert_comp(smt::PrimOp::BVUle, terms.terms.at(idx2), terms.terms.at(idx1));
          } // has le
          // will always make not eq
          if (has_eq)
            insert_comp(smt::PrimOp::Distinct, terms.terms.at(idx1), terms.terms.at(idx2));
        } else { // v1 == v2
          if (has_le) {
            insert_comp(smt::PrimOp::BVUle, terms.terms.at(idx1), terms.terms.at(idx2));
            insert_comp(smt::PrimOp::BVUle, terms.terms.at(idx2), terms.terms.at(idx1));
          } // has le
          // will always make eq
          if (has_eq)
            insert_comp(smt::PrimOp::Equal, terms.terms.at(idx1), terms.terms.at(idx2));
        } // v1 =?= v2
      } // for idx2
    } // for idx1 

    terms.set_all_comp_pointers( terms.terms.size() );
    

  assert (predicate_list_btor_.size() == predicate_list_msat_.size());
  assert (predicate_list_btor_.size() == predicate_list_btor_next_.size());
  
  GlobalTimer.RegisterEventEnd("Enum.PredicateGen", predicate_list_btor_.size());

} // PopulatePredicateListsWithTermsIncr


Enumerator::MoreTermPredResult Enumerator::MoreTermPredicates() { // more terms & predicates
  // for each width decide the policy
  width_term_policy_table_t policy; // we can decide the policy after one pass
  bool new_policy = MoreTermPredicateGetPolicy(policy);
  if (!new_policy) // if we have no strategy to proceed, then fail
    return MoreTermPredResult::NO_NEW_POLICY;

  width_new_terms_t new_terms_on_other_width;
  for (auto & width_term_pair : width_term_table_) {
    auto width = width_term_pair.first;
    auto & terms = width_term_pair.second;

    auto policy_pos = policy.find(width);
    if (policy_pos == policy.end())
      continue;
    
    if (policy_pos->second.term_op == term_policy::term_action_t::OP) {
      PopulateTermTableWithUnaryOp(width, terms, policy_pos->second.op_start, policy_pos->second.op_end );
      PopulateTermTableWithBinaryOp(width, terms, policy_pos->second.op_start, policy_pos->second.op_end );
      // if start == end == 0, then will use all
    } else if (policy_pos->second.term_op == term_policy::term_action_t::TERM_3) {
      ReplaceTermWithTrans3(width, terms, new_terms_on_other_width);
    }
  }

#if TERM_TABLE_DEBUG_LVL == 1
  // a light weight dump function
  PrintWidthTermTableSimple(width_term_table_);
#endif
#if TERM_TABLE_DEBUG_LVL == 2
  PrintWidthTermTable(width_term_table_);
#endif

  for (auto && width_term_pair : new_terms_on_other_width) {
    auto width = width_term_pair.first;
    auto & terms = width_term_pair.second; // this is just btor terms

    auto existing_term_pos = width_term_table_.find(width);
    if (existing_term_pos == width_term_table_.end()) {
      // TODO: you need to create!
      // remember to check term_string to avoid dup insert
      // Populate consts if there is not -> const (per width)
      // set nvars = 0
      // set existing_term_pos
      // add policy -> set 0
    }
    // add terms (and their translate)
    

  }


  // create predconjs
  for (auto & width_term_pair : width_term_table_) {
    auto width = width_term_pair.first;
    auto & terms = width_term_pair.second;

    auto policy_pos = policy.find(width);
    if (policy_pos == policy.end()) {
      // this is due to added terms
      continue;
    }

    if (policy_pos->second.term_op != term_policy::term_action_t::NONE) {
      // all of op term3 and comp needs to populate 
      terms.term_policy_action = policy_pos->second.action;
      PopulatePredicateListsWithTermsIncr(width, terms, 
        policy_pos->second.cmp_start,policy_pos->second.cmp_end );
    }
  } // end of for each width


  if (predicate_list_btor_.size() <= enum_status_.curr_predicate_num)
    return MoreTermPredResult::TRY_AGAIN; // although we may come up with more terms, they do not make more preds

  enum_status_.increase_predicate_num();
  return MoreTermPredResult::SUCCEEDED;
} // MoreTermPredicates


void Enumerator::MoreConjunctions() { // more conjunction
  curr_conjunction_depth ++; 
}
void Enumerator::ResetConjunctionOne() { // restart from 1 conjunction
  curr_conjunction_depth = 1;
}


std::pair<smt::Term, smt::Term> Enumerator::EnumCurrentLevel(uint64_t bnd) {
  uint64_t idx = 0;
  D(0, "[sat-enum] receive init {} , prop {}", (init_->to_string()), (prop_ == NULL ? "None": prop_->to_string())  );
  GlobalTimer.RegisterEventStart("Enum.EnumPredConj", idx);

  while(true) {
    if(bnd != 0 && idx > bnd) {
      GlobalTimer.RegisterEventEnd("Enum.EnumPredConj", idx);
      return std::make_pair(nullptr,nullptr);
    }
    ++ idx;

    bool cand_exists = enum_status_.next_pred_assignment(curr_conjunction_depth);
    if (!cand_exists) {
      GlobalTimer.RegisterEventEnd("Enum.EnumPredConj", idx);
      return std::make_pair(nullptr,nullptr);
    }
    
    smt::Term raw_cand = enum_status_.GetCandidateBtor(solver_);
    smt::Term cand = NOT(raw_cand);
    D(0, "[EnumCurrentLevel] : cand : {}", cand->to_string());
    // fact => cand
    // init => cand
    if (!compatible_w_facts(cand))
      continue;
    if (!init_imply(cand))
      continue;
    smt::Term cand_next = NOT(enum_status_.GetCandidateBtorNext(solver_));
    if (!F_T_and_P_imply_Pprime(cand, cand_next))
      continue;
    smt::Term cand_msat = NOT_msat(enum_status_.GetCandidateMsat(msat_solver_));

    GlobalTimer.RegisterEventEnd("Enum.EnumPredConj", idx);
    return std::make_pair(cand, cand_msat);
  }
  assert (false); // nonreachable

  GlobalTimer.RegisterEventEnd("Enum.EnumPredConj", idx);
  return std::make_pair(nullptr,nullptr);
} // EnumCurrentLevel


void Enumerator::PrintWidthTermTableSimple(const width_term_table_t & tb) {
  for(const auto & width_terms_pair : tb) {
    auto width = width_terms_pair.first;
    const auto & terms_info = width_terms_pair.second;

    auto nv = terms_info.n_vars;
    auto nc = terms_info.n_consts_vars - terms_info.n_vars;
    auto nt = terms_info.terms.size() - terms_info.n_consts_vars;

    if(nv == 0 && (nt == 0) ) {
      // if no vars and no consts
      std::cout << "[Width = " << width << "]" 
        << " V:" << nv ;
      if (nc != 0) {
        std::cout << " C:";
        if (nc == 1)
          std::cout << ((terms_info.terms.at(terms_info.n_vars).first)->to_string()) << " (1) ";
        else
          std::cout << ((terms_info.terms.at( terms_info.n_vars ).first)->to_string()) << " .. "
                    << ((terms_info.terms.at( terms_info.n_consts_vars -1).first)->to_string()) <<  " (" << nc << ")";
      }
      std::cout << " T:" << nt 
        << " , skip." << std::endl;
      continue; // skip those without vars;
    }

    std::cout << "[Width = " << width << "] "
              << "[PU @ " << terms_info.prev_unary_pointer 
              << ", PB @ " << terms_info.prev_binary_pointer
              << ", PC @ " << terms_info.prev_eq_pointer << "," 
                           << terms_info.prev_comp_lt_pointer << ","
                           << terms_info.prev_comp_le_pointer << " ]" << std::endl;

    std::cout << "  V : ";
    if (nv == 0)
      std::cout << " (none) " << std::endl;
    else if (nv == 1)
      std::cout << ((terms_info.terms.at(0).first)->to_string()) << " (1) " << std::endl;
    else
      std::cout << ((terms_info.terms.at(0).first)->to_string()) << " .. "
                << ((terms_info.terms.at( terms_info.n_vars - 1 ) .first)->to_string()) <<  "(" << nv << ")" << std::endl;
    
    std::cout << "  C : ";
    if (nc == 0)
      std::cout << " (none) " << std::endl;
    else if (nc == 1)
      std::cout << ((terms_info.terms.at(terms_info.n_vars).first)->to_string()) << " (1) "<< std::endl;
    else
      std::cout << ((terms_info.terms.at( terms_info.n_vars ).first)->to_string()) << " .. "
                << ((terms_info.terms.at( terms_info.n_consts_vars -1).first)->to_string()) <<  " (" << nc << ")" << std::endl;
    
    std::cout << "  T : ";
    if (nt == 0)
      std::cout << " (none) " << std::endl;
    else if (nt == 1)
      std::cout << ((terms_info.terms.at(terms_info.n_consts_vars).first)->to_string()) << " (1) "<< std::endl;
    else
      std::cout << ((terms_info.terms.at(terms_info.n_consts_vars).first)->to_string()) << " .. "
                << ((terms_info.terms.at(terms_info.terms.size()-1).first)->to_string()) <<  " (" << nt << ")" << std::endl;

    { // end of estimate term num
      size_t unary_op_num = 0, binary_op_num = 0, comp_op_num = 0;
      auto pos = syntax_struct_.find(width);
      if (pos != syntax_struct_.end()) {
        unary_op_num = pos->second.op_unary.size();
        binary_op_num = pos->second.op_binary.size();
      }
      const auto & comp_op = GetCompForWidth(width);
      bool has_lt = IN(smt::PrimOp::BVUlt, comp_op) && width > 1; // 0 or 1, then eq/neq are good
      bool has_le = IN(smt::PrimOp::BVUle, comp_op) && width > 1;
      comp_op_num = 1 + (has_lt?1:0) + (has_le?1:0);
      auto after_unary = (nv+nc)*(unary_op_num) + nv + nc;
      auto after_binary = after_unary*(after_unary-1)*binary_op_num/2; // possibly symmetry
      auto npred = after_binary*(after_binary-1)/2;
      std::cout << "  #uop: " << unary_op_num << " #bop: " << binary_op_num << "  Estimate #T: " << after_binary << ", #pred: " << npred << std::endl;
    } // end of estimate term num

    // ops dump & estimate count
    // estimate pred
  }
} // PrintWidthTermTableSimple

void Enumerator::PrintWidthTermTable(const width_term_table_t & tb) {
  for(const auto & width_terms_pair : tb) {
    auto width = width_terms_pair.first;
    const auto & terms_info = width_terms_pair.second;
    std::cout << "[Width = " << width << "]" << std::endl;
    std::cout << "[PU @ " << terms_info.prev_unary_pointer 
              << ", PB @ " << terms_info.prev_binary_pointer
              << ", PC @ " << terms_info.prev_eq_pointer << "," 
                           << terms_info.prev_comp_lt_pointer << ","
                           << terms_info.prev_comp_le_pointer << " ]" << std::endl;
    std::cout << "V : ";
    unsigned idx = 0;
    for (; idx < terms_info.n_vars; ++idx )
      std::cout << ((terms_info.terms.at(idx).first)->to_string()) << ",";
    std::cout << std::endl;

    std::cout << "C : ";
    for (; idx < terms_info.n_consts_vars; ++idx )
      std::cout << ((terms_info.terms.at(idx).first)->to_string()) << ",";
    std::cout << std::endl;

    std::cout << "T : ";
    for (; idx < terms_info.terms.size(); ++idx )
      std::cout << ((terms_info.terms.at(idx).first)->to_string()) << ",";
    std::cout << std::endl;
    std::cout << std::endl;
  }
} // PrintWidthTermTable

void Enumerator::PrintEnumStatus(const enum_status & e) {
  e.dump();
}



} // namespace policy_sat_enum

} // namespace cosa
