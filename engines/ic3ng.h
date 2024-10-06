/*********************                                                  */
/*! \file ic3ng.h
** \verbatim
** Top contributors (to current version):
**   Hongce Zhang
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
*/

// IC3 New
//   save the Model
//   use Bitwuzla
//   lemma class
//   varset could contain (_ extract .. )
//   labeling for solver
//   step 1: bit-level
//  
//   multiple inductive gen for 1 cex
//   also need to maintain cex -> word-level pointer & which frame it has been pushed to
//   frame contains only unpushed lemmas


#pragma once


#include <algorithm>
#include <queue>
#include <fstream>

#include "engines/prover.h"
#include "smt-switch/utils.h"
#include "ic3ng-support/lemma.h"
#include "ic3ng-support/priority_queue.h"
#include "utils/partial_model.h"


namespace pono
{
  class IC3ng : public Prover, public ModelLemmaManager {
    // type definition
    typedef std::vector<Lemma *> frame_t;
    typedef std::unordered_set<smt::Term> varset_t;
    typedef std::vector<Model *> facts_t;

  public:
    IC3ng(const Property & p, const TransitionSystem & ts,
            const smt::SmtSolver & s,
            PonoOptions opt = PonoOptions());
    virtual void initialize() override;
    virtual ProverResult check_until(int k) override;
    ProverResult step(int i);

    virtual ~IC3ng(); // for lower cost, we will manage the memory ourselves
    // and disallow copy constructor and etc.
    IC3ng & operator=(const IC3ng &) = delete;
    IC3ng(const IC3ng &) = delete;

    smt::SmtSolver & solver() override { return solver_; }
    std::string print_frame_stat() const ;
    void print_time_stat(std::ostream & os) const ;

  protected:
    std::ofstream debug_fout;
    bool has_assumptions;
    // this is used to cut input
    void cut_vars_curr(std::unordered_map<smt::Term,std::vector<std::pair<int,int>>> & v, bool cut_curr_input);

    PartialModelGen partial_model_getter;

    // will only keep those not pushed yet
    std::vector<frame_t> frames;
    
    // labels for activating assertions
    smt::Term init_label_;       ///< label to activate init
    // smt::Term constraint_label_; ///< label to activate constraints // you can avoid this, because it is directly added to frame
    // smt::Term trans_label_;      ///< label to activate trans // you can avoid using trans_ most of the time
    smt::TermVec frame_labels_;  ///< labels to activate frames
    // useful terms
    smt::Term solver_true_;

    smt::Sort boolsort_;

    virtual void check_ts();
    smt::Term get_trans_for_vars(const smt::UnorderedTermSet & vars);

    // some ts related info buffers
    smt::Term bad_next_trans_subst_;

    smt::UnorderedTermSet actual_statevars_;
    smt::UnorderedTermSet no_next_vars_; //  the inputs
    smt::UnorderedTermSet no_next_vars_nxt_; //  the next state of inputs
    smt::Term all_constraints_; // all constraints
    smt::Term init_prime_;
    smt::UnorderedTermMap nxt_state_updates_; // a map from prime var -> next
    smt::Term next_trans_replace(const smt::Term & in) const {
      return ts_.solver()->substitute(in, nxt_state_updates_);
    } // replace next variables with their update function
    
    Ic3PriorityQueue proof_goals;
    
    /** Perform the base IC3 step (zero case)
     */
    bool check_init_failed(); // return true if failed

    void append_frame();
    void add_lemma_to_frame(Lemma * lemma, unsigned fidx);

    // will also cancel out other frame labels
    void assert_frame(unsigned fidx);
    bool frame_implies(unsigned fidx, const smt::Term & expr);
    smt::Term get_frame_formula(unsigned fidx);

    unsigned lowest_frame_touched_;
    bool recursive_block_all_in_queue(); // recursive_block_all_in_queue will update lowest_frame_touched_
    bool last_frame_reaches_bad();
    void eager_push_lemmas(unsigned fidx, unsigned start_lemma_id);

    bool push_lemma_to_new_frame(); // will use lowest_frame_touched_ to start from
    void validate_inv();
    void inductive_generalization(unsigned fidx, Model *cex, LCexOrigin origin);

    void reduce_unsat_core_linear_backwards(const smt::Term & F_and_T,
      smt::TermList &conjs, smt::TermList & conjs_nxt);

    // \neg C /\ F /\ C
    //           F /\ p
    ic3_rel_ind_check_result rel_ind_check( unsigned prevFidx, 
      const smt::Term & bad_next_trans_subst_,
      Model * cex_to_block,
      bool get_pre_state );

    void extend_predicates(Model *cex, smt::TermVec & conj_inout);
    void load_predicates(const std::string & fname);
    smt::TermVec loaded_predicates_;
    std::unordered_map<Model *, PerCexInfo> model_info_map_;

    /**
     * misc functions, supportive functions
    */
    void sanity_check_cex_is_correct(fcex_t *cex_at_cycle_0);

    // can_sat is used to ensure SAT[init] and SAT[init/\T]
    bool can_sat(const smt::Term & t);

    smt::Term smart_not(const smt::Term & in) {
      const smt::Op &op = in->get_op();
      if (op == smt::Not) {
        smt::TermVec children(in->begin(), in->end());
        assert(children.size() == 1);
        return children[0];
      } else {
        return solver_->make_term(smt::Not, in);
      }
    } // end of smart_not
    template<typename T>
    smt::Term smart_and(const T & in) {
      assert(in.size());
      smt::Term term = *(in.begin());
      for (auto iter = ++(in.begin()); iter!=in.end(); ++iter) {
        term = solver_->make_term(smt::And, term, *iter);
      }
      return term;
    }
    template<typename T>
    smt::Term smart_or(const T & in) {
      assert(in.size());
      smt::Term term = *(in.begin());
      for (auto iter = ++(in.begin()); iter!=in.end(); ++iter) {
        term = solver_->make_term(smt::Or, term, *iter);
      }
      return term;
    }

  }; // end of class IC3ng

} // namespace pono

