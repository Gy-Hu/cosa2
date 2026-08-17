/*********************                                                  */
/*! \file ic3ia.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Ahmed Irfan
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief IC3 via Implicit Predicate Abstraction (IC3IA) implementation
**        based on
**
**        IC3 Modulo Theories via Implicit Predicate Abstraction
**            -- Alessandro Cimatti, Alberto Griggio,
**               Sergio Mover, Stefano Tonetta
**
**        and the open source implementation:
**
**        https://es-static.fbk.eu/people/griggio/ic3ia/index.html
**
**  within Pono, we are building on the bit-level IC3 instead of directly
**  on IC3Base, because a lot of the functionality is the same
**  In particular, we don't need to override either of the generalization
**  functions. Instead focusing on abstract/refine.
**
**/

#pragma once

#include <cstddef>
#include <string>

#include "core/prop.h"
#include "core/refineresult.h"
#include "core/ts.h"
#include "engines/ic3.h"
#include "modifiers/implicit_predicate_abstractor.h"
#include "options/options.h"
#include "smt-switch/smt.h"
#include "utils/cegp_bandit.h"

namespace pono {

class IC3IA : public IC3
{
 public:
  // itp_se is the SolverEnum for the interpolator

  IC3IA(const SafetyProperty & p,
        const TransitionSystem & ts,
        const smt::SmtSolver & solver,
        PonoOptions opt = {},
        Engine engine = Engine::IC3IA_ENGINE);

  typedef IC3 super;

  void add_important_var(smt::Term v);

  void finish_fallback_bandit(ProverResult result);

 protected:
  bool compute_witness() override;

  // Note: important that conc_ts_ and abs_ts_ are before ia_
  //       because we will pass them to ia_ and they must be
  //       be initialized first

  TransitionSystem conc_ts_;

  ImplicitPredicateAbstractor ia_;

  smt::UnorderedTermSet predset_;  ///< set of current predicates
  // useful for checking if predicate has been added already
  // also available as a vector in ia_.predicates()

  smt::SmtSolver interpolator_;  ///< interpolator for refinement
  smt::TermTranslator
      to_interpolator_;  ///< transfer terms from solver_ to interpolator_
  smt::TermTranslator
      to_solver_;  ///< transfer terms from interpolator_ to solver_

  size_t longest_cex_length_;  ///< keeps track of longest (abstract)
                               ///< counterexample

  ThreeArmUcbController fallback_bandit_;
  bool fallback_bandit_pending_ = false;
  size_t fallback_bandit_arm_ = 0;
  IC3EpochStatistics fallback_bandit_start_;

  void update_fallback_bandit(ProverResult result);

  IC3IARefinementUcbController refinement_packet_bandit_;
  bool refinement_packet_pending_ = false;
  bool refinement_packet_learning_ = false;
  IC3IARefinementPacket refinement_packet_ = IC3IARefinementPacket::LEAN_CORE;
  IC3EpochStatistics refinement_packet_start_;
  size_t refinement_packet_predicates_added_ = 0;
  size_t refinement_packet_reducer_queries_ = 0;
  size_t refinement_packet_reducer_queries_charged_ = 0;
  size_t refinement_packet_reducer_queries_for_decision_ = 0;
  double refinement_packet_cpu_seconds_for_decision_ = 0.0;
  size_t refinement_decision_id_ = 0;
  size_t repeated_cex_count_ = 0;
  std::string previous_cex_signature_;
  smt::TermVec cached_transition_predicates_;
  bool transition_predicates_cached_ = false;
  smt::UnorderedTermSet important_vars_;

  bool semantic_refinement_packets_enabled() const;
  smt::TermVec transition_predicate_candidates();
  smt::TermVec rank_transition_candidates(const smt::TermVec & candidates,
                                          IC3IARefinementPacket packet) const;
  smt::TermVec build_refinement_packet(
      IC3IARefinementPacket packet,
      const smt::TermVec & interp_core,
      const smt::TermVec & transition_candidates) const;
  bool packet_rules_out_cex(const smt::TermVec & packet);
  void update_refinement_packet(IC3IARefinementPacket packet,
                                size_t predicates_added);
  void finish_refinement_packet(ProverResult result);
  void on_step_finished(ProverResult result) override;

  // Since MathSAT is the best solver for IC3IA it helps to use
  // its bool_model_generation option which doesn't enable
  // model generation for theories
  // instead, we assign indicator labels to check the value of
  // predicates. This should still work fine with other solvers
  smt::UnorderedTermMap lbl2pred_;
  smt::UnorderedTermSet predlbls_;
  smt::UnorderedTermSet all_lbls_;  ///< for debugging assertions only
                                    ///< keeps track of both polarities
                                    ///< mostly needed because some solvers
                                    ///< do automatic top-level propagation
                                    ///< which means you can't count on a symbol
                                    ///< staying a symbol

  /** Overriding the method. This will return the concrete_ts_ because ts_ is an
   *  abstraction of concrete_ts_.
   */
  TransitionSystem & prover_interface_ts() override { return conc_ts_; };
  // pure virtual method implementations

  IC3Formula get_model_ic3formula() const override;

  bool ic3formula_check_valid(const IC3Formula & u) const override;

  // need to override this because IC3IA is not as restricted as
  // (bit-level) IC3
  void check_ts() const override;

  void initialize() override;

  void abstract() override;

  RefineResult refine() override;

  void reset_solver() override;

  bool is_global_label(const smt::Term & l) const override;

  // specific to IC3IA

  void reabstract();

  /** Adds predicate to abstraction
   *  (calls ia_.add_predicate)
   *  and declares a new predicate state var (in pred_statevars_)
   *  @param pred the predicate over current state variables
   *  @return true iff the predicate was new (not seen before)
   */
  bool add_predicate(const smt::Term & pred);

  /** Register a state variable mapping in to_solver_
   *  This is a bit ugly but it's needed because symbols aren't created in
   * to_solver_ so it needs the mapping from interpolator_ symbols to solver_
   * symbols
   *  TODO look into a cleaner solution
   *  @param i the unrolling for state variables
   *         makes sure not to repeat work
   */
  void register_symbol_mappings(size_t i);
};

}  // namespace pono
