/*********************                                                  */
/*! \file ic3ia.cpp
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

#include "engines/ic3ia.h"

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <ctime>
#include <random>
#include <string>
#include <unordered_set>
#include <vector>

#include "core/prop.h"
#include "core/refineresult.h"
#include "core/rts.h"
#include "core/ts.h"
#include "options/options.h"
#include "smt-switch/smt.h"
#include "smt-switch/utils.h"
#include "smt/available_solvers.h"
#include "utils/logger.h"
#include "utils/term_analysis.h"
#include "utils/term_walkers.h"

using namespace smt;
using namespace std;

namespace pono {

IC3IA::IC3IA(const SafetyProperty & p,
             const TransitionSystem & ts,
             const SmtSolver & solver,
             PonoOptions opt,
             Engine engine)
    : super(p, RelationalTransitionSystem(solver), solver, opt, engine),
      conc_ts_(ts, to_prover_solver_),
      ia_(conc_ts_, ts_, unroller_),
      interpolator_(
          create_interpolating_solver_for(options_.smt_interpolator_,
                                          engine_,
                                          options_.printing_smt_interpolator_,
                                          options_.smt_interpolator_opts_)),
      to_interpolator_(interpolator_),
      to_solver_(solver_),
      longest_cex_length_(0),
      fallback_bandit_(0.5),
      refinement_packet_bandit_(0.5)
{
  // since we passed a fresh RelationalTransitionSystem as the main TS
  // need to point orig_ts_ to the right place
  orig_ts_ = ts;
  approx_pregen_ = true;
}

void IC3IA::add_important_var(Term v)
{
  if (!options_.ic3ia_track_important_vars_) {
    return;
  }

  // have to consider that original solver
  // might not be the same as the prover solver
  if (solver_ != orig_ts_.solver()) {
    v = to_prover_solver_.transfer_term(v);
  }
  logger.log(1, "Adding important variable: {}", v);
  ia_.add_important_var(v);
  important_vars_.insert(v);
}

bool IC3IA::semantic_refinement_packets_enabled() const
{
  return options_.mab_ic3ia_refinement_
         || options_.ic3ia_refinement_packet_ > 0;
}

TermVec IC3IA::transition_predicate_candidates()
{
  if (!transition_predicates_cached_) {
    UnorderedTermSet trans_preds;
    get_predicates(solver_, conc_ts_.trans(), trans_preds, false, false, true);
    cached_transition_predicates_.clear();
    cached_transition_predicates_.reserve(trans_preds.size());
    for (const auto & p : trans_preds) {
      Term curr_p = conc_ts_.curr(p);
      if (conc_ts_.only_curr(curr_p)) {
        cached_transition_predicates_.push_back(curr_p);
      }
    }
    std::sort(cached_transition_predicates_.begin(),
              cached_transition_predicates_.end(),
              [](const Term & left, const Term & right) {
                return left->to_string() < right->to_string();
              });
    cached_transition_predicates_.erase(
        std::unique(cached_transition_predicates_.begin(),
                    cached_transition_predicates_.end()),
        cached_transition_predicates_.end());
    transition_predicates_cached_ = true;
  }

  TermVec fresh;
  for (const auto & p : cached_transition_predicates_) {
    if (predset_.find(p) == predset_.end()) {
      fresh.push_back(p);
    }
  }
  return fresh;
}

TermVec IC3IA::rank_transition_candidates(const TermVec & candidates,
                                          IC3IARefinementPacket packet) const
{
  UnorderedTermSet cex_support;
  for (const auto & cube : cex_) {
    get_free_symbolic_consts(cube, cex_support);
  }
  UnorderedTermSet bad_support;
  get_free_symbolic_consts(bad_, bad_support);
  UnorderedTermSet covered_support;
  for (const auto & pred : predset_) {
    get_free_symbolic_consts(pred, covered_support);
  }

  struct RankedPredicate
  {
    Term term;
    double score;
    bool array_related;
    bool important;
    string support_key;
  };
  vector<RankedPredicate> ranked;
  ranked.reserve(candidates.size());
  const unordered_set<PrimOp> array_ops({ Select, Store });
  for (const auto & pred : candidates) {
    UnorderedTermSet support;
    get_free_symbolic_consts(pred, support);
    size_t cex_overlap = 0;
    size_t bad_overlap = 0;
    size_t novel_symbols = 0;
    bool array_related = false;
    bool important = false;
    vector<string> support_names;
    for (const auto & symbol : support) {
      cex_overlap += cex_support.find(symbol) != cex_support.end();
      bad_overlap += bad_support.find(symbol) != bad_support.end();
      novel_symbols += covered_support.find(symbol) == covered_support.end();
      important =
          important || important_vars_.find(symbol) != important_vars_.end();
      array_related =
          array_related || symbol->get_sort()->get_sort_kind() == ARRAY;
      support_names.push_back(symbol->to_string());
    }
    TermOpCollector collector(solver_);
    UnorderedTermSet array_terms;
    collector.find_matching_terms(pred, array_ops, array_terms);
    array_related = array_related || !array_terms.empty();

    std::sort(support_names.begin(), support_names.end());
    string support_key;
    for (const auto & name : support_names) {
      support_key += name;
      support_key += '\n';
    }
    const double score = 4.0 * cex_overlap + 3.0 * bad_overlap
                         + 4.0 * static_cast<double>(array_related)
                         + 5.0 * static_cast<double>(important)
                         + static_cast<double>(novel_symbols);
    ranked.push_back({ pred, score, array_related, important, support_key });
  }

  std::sort(ranked.begin(),
            ranked.end(),
            [](const RankedPredicate & left, const RankedPredicate & right) {
              if (left.score != right.score) {
                return left.score > right.score;
              }
              return left.term->to_string() < right.term->to_string();
            });

  TermVec result;
  unordered_set<string> seen_support;
  TermVec repeated_support;
  for (const auto & candidate : ranked) {
    if (packet == IC3IARefinementPacket::ARRAY_LOCAL && !candidate.array_related
        && !candidate.important) {
      continue;
    }
    if (packet == IC3IARefinementPacket::CEX_DIVERSE
        && !seen_support.insert(candidate.support_key).second) {
      repeated_support.push_back(candidate.term);
      continue;
    }
    result.push_back(candidate.term);
  }
  result.insert(result.end(), repeated_support.begin(), repeated_support.end());
  return result;
}

TermVec IC3IA::build_refinement_packet(
    IC3IARefinementPacket packet,
    const TermVec & interp_core,
    const TermVec & transition_candidates) const
{
  TermVec result = interp_core;
  UnorderedTermSet selected(interp_core.begin(), interp_core.end());
  if (packet == IC3IARefinementPacket::LEAN_CORE) {
    return result;
  }

  const TermVec ranked =
      rank_transition_candidates(transition_candidates, packet);
  size_t limit = 0;
  switch (packet) {
    case IC3IARefinementPacket::ARRAY_LOCAL: limit = 8; break;
    case IC3IARefinementPacket::CEX_DIVERSE: limit = 16; break;
    case IC3IARefinementPacket::RECOVERY:
      limit = options_.ic3ia_fallback_predicates_
                  ? options_.ic3ia_fallback_predicates_
                  : 32;
      break;
    case IC3IARefinementPacket::LEAN_CORE:
    case IC3IARefinementPacket::NUM_PACKETS: break;
  }
  size_t added = 0;
  for (const auto & pred : ranked) {
    if (added >= limit) {
      break;
    }
    if (selected.insert(pred).second) {
      result.push_back(pred);
      added++;
    }
  }
  return result;
}

bool IC3IA::packet_rules_out_cex(const TermVec & packet)
{
  if (packet.empty()) {
    return false;
  }
  TermVec reduced;
  refinement_packet_reducer_queries_++;
  return ia_.reduce_predicates(cex_, packet, reduced);
}

// pure virtual method implementations

IC3Formula IC3IA::get_model_ic3formula() const
{
  TermVec conjuncts;
  conjuncts.reserve(predlbls_.size());
  Term val;
  for (const auto & p : predlbls_) {
    if ((val = solver_->get_value(p)) == solver_true_) {
      conjuncts.push_back(lbl2pred_.at(p));
    } else {
      conjuncts.push_back(solver_->make_term(Not, lbl2pred_.at(p)));
    }
    assert(val->is_value());
  }

  return ic3formula_conjunction(conjuncts);
}

bool IC3IA::ic3formula_check_valid(const IC3Formula & u) const
{
  // check that children are literals
  Term pred;
  Op op;
  for (const auto & c : u.children) {
    if (c->get_sort() != boolsort_) {
      logger.log(3, "ERROR IC3IA IC3Formula contains non-boolean atom: {}", c);
      return false;
    }

    pred = c;
    op = pred->get_op();
    if (op == Not || op == BVNot) {
      pred = *(c->begin());
      assert(pred);
    }

    // expecting either a boolean variable or a predicate
    if (predset_.find(pred) == predset_.end()) {
      logger.log(3, "ERROR IC3IA IC3Formula contains unknown atom: {}", pred);
      return false;
    }
  }

  // got through all checks without failing
  return true;
}

void IC3IA::check_ts() const
{
  // basically a No-Op
  // no restrictions except that interpolants must be supported
  // instead of checking explicitly, just let the interpolator throw an
  // exception better than maintaining in two places
}

void IC3IA::initialize()
{
  if (initialized_) {
    return;
  }

  super::initialize();

  // add all the predicates from init and property to the abstraction
  // NOTE: abstract is called automatically in IC3Base initialize
  UnorderedTermSet preds;
  get_predicates(solver_, conc_ts_.init(), preds, false, false, true);
  size_t num_init_preds = preds.size();
  get_predicates(solver_, bad_, preds, false, false, true);
  size_t num_prop_preds = preds.size() - num_init_preds;
  for (const auto & p : preds) {
    add_predicate(p);
  }
  logger.log(1, "Number predicates found in init: {}", num_init_preds);
  logger.log(1, "Number predicates found in prop: {}", num_prop_preds);
  logger.log(1, "Total number of initial predicates: {}", preds.size());
  // more predicates will be added during refinement
  // these ones are just initial predicates

  // populate cache for existing terms in solver_
  UnorderedTermMap & cache = to_solver_.get_cache();
  Term ns;
  for (auto const & s : ts_.statevars()) {
    // common variables are next states, unless used for refinement in IC3IA
    // then will refer to current state variables after untiming
    // need to cache both
    cache[to_interpolator_.transfer_term(s)] = s;
    ns = ts_.next(s);
    cache[to_interpolator_.transfer_term(ns)] = ns;
  }

  // need to add uninterpreted functions as well
  // first need to find them all
  // NOTE need to use get_free_symbols NOT get_free_symbolic_consts
  // because the latter ignores uninterpreted functions
  UnorderedTermSet free_symbols;
  get_free_symbols(ts_.init(), free_symbols);
  get_free_symbols(ts_.trans(), free_symbols);
  get_free_symbols(bad_, free_symbols);

  for (auto const & s : free_symbols) {
    assert(s->is_symbol());
    if (s->is_symbolic_const()) {
      // ignore constants
      continue;
    }
    cache[to_interpolator_.transfer_term(s)] = s;
  }

  // TODO fix generalize_predecessor for ic3ia
  //      might need to override it
  //      behaves a bit differently with both concrete and abstract next state
  //      vars
  if (options_.ic3_pregen_) {
    logger.log(1,
               "WARNING automatically disabling predecessor generalization -- "
               "not supported in IC3IA yet.");
    options_.ic3_pregen_ = false;
  }
}

void IC3IA::abstract()
{
  const UnorderedTermSet & bool_symbols = ia_.do_abstraction();

  // don't add boolean symbols that are never used in the system
  // this is an optimization and a fix for some options
  // if using mathsat with bool_model_generation
  // it will fail to get the value of symbols that don't
  // appear in the query
  // thus we don't include those symbols in our cubes
  UnorderedTermSet used_symbols;
  get_free_symbolic_consts(ts_.init(), used_symbols);
  get_free_symbolic_consts(ts_.trans(), used_symbols);
  get_free_symbolic_consts(bad_, used_symbols);

  // add predicates automatically added by ia_
  // to our predset_
  // needed to prevent adding duplicate predicates later
  for (const auto & sym : bool_symbols) {
    assert(sym->is_symbolic_const());
    if (used_symbols.find(sym) != used_symbols.end()) {
      add_predicate(sym);
    }
  }

  assert(ts_.init());  // should be non-null
  assert(ts_.trans());
}

RefineResult IC3IA::refine()
{
  // counterexample trace should have been populated
  assert(cex_.size());
  if (cex_.size() == 1) {
    // if there are no transitions, then this is a concrete CEX
    return REFINE_NONE;
  }
  const clock_t refinement_start_clock = std::clock();

  size_t cex_length = cex_.size();

  // use interpolator to get predicates
  // remember -- need to transfer between solvers
  assert(interpolator_);

  TermVec formulae;
  for (size_t i = 0; i < cex_length; ++i) {
    // make sure to_solver_ cache is populated with unrolled symbols
    register_symbol_mappings(i);
    Term t;
    if (options_.ic3ia_sim_cex_) {
      // simulate abstract cex
      t = unroller_.at_time(cex_[i], i);
    } else {
      // perform BMC using Init and P
      if (i == 0) {
        t = unroller_.at_time(conc_ts_.init(), i);
      } else if (i + 1 == cex_length) {
        t = unroller_.at_time(bad_, i);
      } else {
        t = solver_->make_term(Not, unroller_.at_time(bad_, i));
      }
    }
    if (i + 1 < cex_length) {
      t = solver_->make_term(And, t, unroller_.at_time(conc_ts_.trans(), i));
    }
    formulae.push_back(to_interpolator_.transfer_term(t, BOOL));
  }

  TermVec out_interpolants;
  Result r =
      interpolator_->get_sequence_interpolants(formulae, out_interpolants);

  if (r.is_sat()) {
    // this is a real counterexample, so the property is false
    return RefineResult::REFINE_NONE;
  }

  // record the length of this counterexample
  // important to set it here because it's used in register_symbol_mapping
  // to determine if state variables unrolled to a certain length
  // have already been cached in to_solver_
  longest_cex_length_ = cex_length;

  UnorderedTermSet preds;
  for (auto const & I : out_interpolants) {
    if (!I) {
      assert(
          r.is_unknown());  // should only have null terms if got unknown result
      continue;
    }

    Term solver_I = unroller_.untime(to_solver_.transfer_term(I, BOOL));
    assert(conc_ts_.only_curr(solver_I));
    logger.log(3, "got interpolant: {}", solver_I);
    get_predicates(solver_, solver_I, preds, false, false, true);
  }

  // new predicates
  TermVec fresh_preds;
  for (auto const & p : preds) {
    if (predset_.find(p) == predset_.end()) {
      // unseen predicate
      fresh_preds.push_back(p);
    }
  }

  if (semantic_refinement_packets_enabled()) {
    TermVec interp_core = fresh_preds;
    if (options_.ic3ia_reduce_preds_ && !fresh_preds.empty()) {
      TermVec reduced;
      refinement_packet_reducer_queries_++;
      if (ia_.reduce_predicates(cex_, fresh_preds, reduced)
          && !reduced.empty()) {
        interp_core = reduced;
      }
    }

    const TermVec transition_candidates = transition_predicate_candidates();
    array<bool, IC3IARefinementUcbController::num_arms> valid{};
    valid[static_cast<size_t>(IC3IARefinementPacket::LEAN_CORE)] =
        !interp_core.empty();
    valid[static_cast<size_t>(IC3IARefinementPacket::ARRAY_LOCAL)] =
        !rank_transition_candidates(transition_candidates,
                                    IC3IARefinementPacket::ARRAY_LOCAL)
             .empty();
    valid[static_cast<size_t>(IC3IARefinementPacket::CEX_DIVERSE)] =
        !transition_candidates.empty();
    valid[static_cast<size_t>(IC3IARefinementPacket::RECOVERY)] =
        !transition_candidates.empty() || !interp_core.empty();
    size_t valid_count = 0;
    for (bool is_valid : valid) {
      valid_count += is_valid;
    }
    if (!valid_count) {
      logger.log(1,
                 "IC3IA: refinement failed couldn't find any semantic "
                 "packet candidates");
      return RefineResult::REFINE_FAIL;
    }

    vector<string> cex_terms;
    cex_terms.reserve(cex_.size());
    for (const auto & cube : cex_) {
      cex_terms.push_back(cube->to_string());
    }
    std::sort(cex_terms.begin(), cex_terms.end());
    string cex_signature;
    for (const auto & term : cex_terms) {
      cex_signature += term;
      cex_signature += '\n';
    }
    if (cex_signature == previous_cex_signature_) {
      repeated_cex_count_++;
    } else {
      previous_cex_signature_ = cex_signature;
      repeated_cex_count_ = 0;
    }

    IC3IARefinementPacket packet = IC3IARefinementPacket::RECOVERY;
    bool learning_opportunity =
        options_.mab_ic3ia_refinement_ && valid_count > 1;
    if (learning_opportunity) {
      packet = refinement_packet_bandit_.select(valid);
    } else if (options_.ic3ia_refinement_packet_) {
      packet = static_cast<IC3IARefinementPacket>(
          options_.ic3ia_refinement_packet_ - 1);
      if (!valid[static_cast<size_t>(packet)]) {
        packet = IC3IARefinementPacket::RECOVERY;
      }
    } else {
      for (size_t arm = 0; arm < valid.size(); ++arm) {
        if (valid[arm]) {
          packet = static_cast<IC3IARefinementPacket>(arm);
          break;
        }
      }
    }
    if (repeated_cex_count_ >= 2
        && valid[static_cast<size_t>(IC3IARefinementPacket::RECOVERY)]) {
      packet = IC3IARefinementPacket::RECOVERY;
      learning_opportunity = false;
    }

    TermVec selected =
        build_refinement_packet(packet, interp_core, transition_candidates);
    bool expanded = false;
    bool safe_fallback = false;
    if (interp_core.empty() && !packet_rules_out_cex(selected)) {
      expanded = true;
      TermVec expansion = rank_transition_candidates(
          transition_candidates, IC3IARefinementPacket::RECOVERY);
      UnorderedTermSet selected_set(selected.begin(), selected.end());
      size_t expansion_target =
          std::max<size_t>(selected.size() + 1, selected.size() * 2);
      size_t expansion_pos = 0;
      while (expansion_pos < expansion.size()) {
        while (expansion_pos < expansion.size()
               && selected.size() < expansion_target) {
          if (selected_set.insert(expansion[expansion_pos]).second) {
            selected.push_back(expansion[expansion_pos]);
          }
          expansion_pos++;
        }
        if (packet_rules_out_cex(selected)) {
          break;
        }
        expansion_target =
            std::min(expansion.size(),
                     std::max(expansion_target + 1, expansion_target * 2));
      }
      if (expansion_pos == expansion.size()
          && !packet_rules_out_cex(selected)) {
        // Preserve the legacy sound fallback when a reducer cannot establish
        // progress (for example because UF unrolling forces incompatible
        // interpretations).  The full fresh pool is still added.
        safe_fallback = true;
      }
    }

    if (selected.empty()) {
      logger.log(1, "IC3IA: semantic refinement packet is empty");
      return RefineResult::REFINE_FAIL;
    }
    for (const auto & pred : selected) {
      const bool new_pred = add_predicate(pred);
      assert(new_pred);
    }
    refinement_decision_id_++;
    refinement_packet_learning_ = learning_opportunity;
    refinement_packet_cpu_seconds_for_decision_ =
        static_cast<double>(std::clock() - refinement_start_clock)
        / CLOCKS_PER_SEC;
    logger.log(0,
               "IC3IA-REFINEMENT select id={} round={} packet={} learning={} "
               "valid={} interp={} transition={} selected={} repeated={} "
               "expanded={} safe_fallback={}",
               refinement_decision_id_,
               refinement_packet_bandit_.rounds(),
               to_string(packet),
               learning_opportunity,
               valid_count,
               interp_core.size(),
               transition_candidates.size(),
               selected.size(),
               repeated_cex_count_,
               expanded,
               safe_fallback);
    update_refinement_packet(packet, selected.size());
    logger.log(1,
               "{} new predicates added by semantic refinement packet",
               selected.size());
    return RefineResult::REFINE_SUCCESS;
  }

  if (!fresh_preds.size() && options_.ic3ia_fallback_predicates_) {
    update_fallback_bandit(ProverResult::UNKNOWN);

    UnorderedTermSet trans_preds;
    get_predicates(solver_, conc_ts_.trans(), trans_preds, false, false, true);
    UnorderedTermSet fallback_set;
    for (const auto & p : trans_preds) {
      Term curr_p = conc_ts_.curr(p);
      if (conc_ts_.only_curr(curr_p)
          && predset_.find(curr_p) == predset_.end()) {
        fallback_set.insert(curr_p);
      }
    }
    fresh_preds.insert(
        fresh_preds.end(), fallback_set.begin(), fallback_set.end());
    std::sort(fresh_preds.begin(),
              fresh_preds.end(),
              [](const Term & left, const Term & right) {
                return left->to_string() < right->to_string();
              });
    size_t fallback_limit = options_.ic3ia_fallback_predicates_;
    if (options_.cegp_bandit_ && fresh_preds.size()) {
      fallback_bandit_arm_ = fallback_bandit_.select();
      if (fallback_bandit_arm_ == 1) {
        fallback_limit = std::max<size_t>(1, (fallback_limit + 1) / 2);
      } else if (fallback_bandit_arm_ == 2) {
        fallback_limit = std::max<size_t>(1, (fallback_limit + 3) / 4);
      }
      fallback_bandit_start_ = epoch_statistics();
      fallback_bandit_pending_ = true;
      logger.log(0,
                 "IC3IA-FALLBACK-BANDIT select round={} arm={} limit={} "
                 "candidates={}",
                 fallback_bandit_.rounds(),
                 fallback_bandit_arm_,
                 fallback_limit,
                 fresh_preds.size());
    }
    if (fresh_preds.size() > fallback_limit) {
      fresh_preds.resize(fallback_limit);
    }
    logger.log(1,
               "IC3IA: interpolation stalled, using {} transition predicate "
               "fallback(s)",
               fresh_preds.size());
  }

  if (!fresh_preds.size()) {
    logger.log(1, "IC3IA: refinement failed couldn't find any new predicates");
    return RefineResult::REFINE_FAIL;
  }

  if (options_.random_seed_ > 0) {
    shuffle(fresh_preds.begin(),
            fresh_preds.end(),
            default_random_engine(options_.random_seed_));
  }

  // reduce new predicates
  TermVec red_preds;
  if (options_.ic3ia_reduce_preds_
      && ia_.reduce_predicates(cex_, fresh_preds, red_preds)) {
    // reduction successful
    logger.log(2,
               "reduce predicates successful {}/{}",
               red_preds.size(),
               fresh_preds.size());
    if (red_preds.size() < fresh_preds.size()) {
      fresh_preds.clear();
      fresh_preds.insert(fresh_preds.end(), red_preds.begin(), red_preds.end());
    }
  } else {
    // if enabled should only fail if removed all predicates
    // this can happen when there are uninterpreted functions
    // the unrolling can force incompatible UF interpretations
    // but IC3 (which doesn't unroll) still needs the predicates
    // in this case, just use all the fresh predicates
    assert(!options_.ic3ia_reduce_preds_ || red_preds.size() == 0);
    logger.log(2, "reduce predicates FAILED");
  }

  // add all the new predicates
  for (auto const & p : fresh_preds) {
    bool new_pred = add_predicate(p);
    // expect all predicates to be new (e.g. unseen)
    // they were already filtered above
    assert(new_pred);
  }

  logger.log(1, "{} new predicates added by refinement", fresh_preds.size());

  // able to refine the system to rule out this abstract counterexample
  return RefineResult::REFINE_SUCCESS;
}

void IC3IA::finish_fallback_bandit(ProverResult result)
{
  update_fallback_bandit(result);
}

void IC3IA::update_fallback_bandit(ProverResult result)
{
  if (!fallback_bandit_pending_) {
    return;
  }

  const IC3EpochStatistics & current = epoch_statistics();
  const size_t attempts = current.propagation_attempts
                          - fallback_bandit_start_.propagation_attempts;
  const size_t successes = current.propagation_successes
                           - fallback_bandit_start_.propagation_successes;
  const size_t frontier =
      current.propagation_successes_to_frontier
      - fallback_bandit_start_.propagation_successes_to_frontier;
  const size_t frames =
      current.frames_created - fallback_bandit_start_.frames_created;
  const double push_rate =
      attempts ? static_cast<double>(successes) / attempts : 0.0;
  const double frontier_rate =
      attempts ? static_cast<double>(frontier) / attempts : 0.0;
  const double frame_progress =
      std::min(1.0, static_cast<double>(frames) / 4.0);
  const double terminal_progress =
      result == ProverResult::TRUE
          ? 1.0
          : (result == ProverResult::FALSE ? 0.5 : 0.0);
  const double reward = 0.45 * push_rate + 0.15 * frontier_rate
                        + 0.15 * frame_progress + 0.25 * terminal_progress;
  fallback_bandit_.update(fallback_bandit_arm_, reward);
  logger.log(0,
             "IC3IA-FALLBACK-BANDIT update round={} arm={} reward={} "
             "push={}/{} frontier={} frames={} result={}",
             fallback_bandit_.rounds(),
             fallback_bandit_arm_,
             reward,
             successes,
             attempts,
             frontier,
             frames,
             result);
  fallback_bandit_pending_ = false;
}

void IC3IA::update_refinement_packet(IC3IARefinementPacket packet,
                                     size_t predicates_added)
{
  if (refinement_packet_pending_) {
    logger.log(0,
               "IC3IA-REFINEMENT censored id={} reason=new_refinement",
               refinement_decision_id_ - 1);
  }
  refinement_packet_ = packet;
  refinement_packet_start_ = epoch_statistics();
  refinement_packet_predicates_added_ = predicates_added;
  refinement_packet_reducer_queries_for_decision_ =
      refinement_packet_reducer_queries_
      - refinement_packet_reducer_queries_charged_;
  refinement_packet_reducer_queries_charged_ =
      refinement_packet_reducer_queries_;
  refinement_packet_pending_ = true;
}

void IC3IA::finish_refinement_packet(ProverResult result)
{
  if (!refinement_packet_pending_) {
    return;
  }

  const IC3EpochStatistics & current = epoch_statistics();
  const size_t attempts = current.propagation_attempts
                          - refinement_packet_start_.propagation_attempts;
  const size_t successes = current.propagation_successes
                           - refinement_packet_start_.propagation_successes;
  const size_t frontier =
      current.propagation_successes_to_frontier
      - refinement_packet_start_.propagation_successes_to_frontier;
  const size_t frames =
      current.frames_created - refinement_packet_start_.frames_created;
  const size_t queries =
      current.solver_queries - refinement_packet_start_.solver_queries;
  const double push_rate =
      attempts ? static_cast<double>(successes) / attempts : 0.0;
  const double frontier_rate =
      attempts ? static_cast<double>(frontier) / attempts : 0.0;
  const double frame_progress =
      std::min(1.0, static_cast<double>(frames) / 2.0);
  const double terminal_progress = result == ProverResult::TRUE ? 1.0 : 0.0;
  const double progress = 0.35 * frame_progress + 0.30 * push_rate
                          + 0.20 * frontier_rate + 0.15 * terminal_progress;
  const double query_cost =
      std::min(1.0, std::log1p(static_cast<double>(queries)) / std::log(33.0));
  const double predicate_cost = std::min(
      1.0, static_cast<double>(refinement_packet_predicates_added_) / 32.0);
  const double reducer_cost = std::min(
      1.0,
      static_cast<double>(refinement_packet_reducer_queries_for_decision_)
          / 4.0);
  const double refinement_cpu_cost = std::min(
      1.0,
      std::log1p(refinement_packet_cpu_seconds_for_decision_) / std::log(11.0));
  const double reward = std::max(
      -1.0,
      std::min(1.0,
               progress - 0.10 * query_cost - 0.12 * predicate_cost
                   - 0.05 * reducer_cost - 0.08 * refinement_cpu_cost));
  if (refinement_packet_learning_) {
    refinement_packet_bandit_.update(refinement_packet_, reward);
  }
  logger.log(0,
             "IC3IA-REFINEMENT update id={} round={} packet={} learning={} "
             "reward={} progress={} queries={} reducer_queries={} "
             "refinement_cpu={} predicates={} push={}/{} frontier={} "
             "frames={} result={}",
             refinement_decision_id_,
             refinement_packet_bandit_.rounds(),
             to_string(refinement_packet_),
             refinement_packet_learning_,
             reward,
             progress,
             queries,
             refinement_packet_reducer_queries_for_decision_,
             refinement_packet_cpu_seconds_for_decision_,
             refinement_packet_predicates_added_,
             successes,
             attempts,
             frontier,
             frames,
             result);
  refinement_packet_pending_ = false;
  refinement_packet_learning_ = false;
}

void IC3IA::on_step_finished(ProverResult result)
{
  finish_refinement_packet(result);
}

void IC3IA::reset_solver()
{
  super::reset_solver();

  for (const auto & elem : lbl2pred_) {
    solver_->assert_formula(solver_->make_term(Equal, elem.first, elem.second));
    Term npred = ts_.next(elem.second);
    Term nlbl = label(npred);
    solver_->assert_formula(solver_->make_term(Equal, nlbl, npred));
  }
}

bool IC3IA::is_global_label(const Term & l) const
{
  // all labels used by IC3IA should be globally assumed
  // the assertion will check that this assumption holds though
  assert(super::is_global_label(l) || all_lbls_.find(l) != all_lbls_.end());
  return true;
}

void IC3IA::reabstract()
{
  // A reabstraction starts a new outer CEGAR epoch, so propagation counters
  // from a pending fallback action are no longer comparable.
  fallback_bandit_pending_ = false;
  if (refinement_packet_pending_) {
    logger.log(0,
               "IC3IA-REFINEMENT censored id={} reason=reabstract "
               "reducer_queries={} predicates={}",
               refinement_decision_id_,
               refinement_packet_reducer_queries_for_decision_,
               refinement_packet_predicates_added_);
    refinement_packet_pending_ = false;
    refinement_packet_learning_ = false;
  }
  transition_predicates_cached_ = false;
  cached_transition_predicates_.clear();

  // don't add boolean symbols that are never used in the system
  // this is an optimization and a fix for some options
  // if using mathsat with bool_model_generation
  // it will fail to get the value of symbols that don't
  // appear in the query
  // thus we don't include those symbols in our cubes
  UnorderedTermSet used_symbols;
  get_free_symbolic_consts(ts_.init(), used_symbols);
  get_free_symbolic_consts(ts_.trans(), used_symbols);
  get_free_symbolic_consts(bad_, used_symbols);

  UnorderedTermSet preds;
  // reset init and trans -- done with calling ia_.do_abstraction
  // then add all boolean constants as (precise) predicates
  for (const auto & p : ia_.do_abstraction()) {
    assert(p->is_symbolic_const());
    if (used_symbols.find(p) != used_symbols.end()) {
      preds.insert(p);
    }
  }

  // predicates from init and bad
  get_predicates(solver_, ts_.init(), preds, false, false, true);
  get_predicates(solver_, bad_, preds, false, false, true);
  // instead of add previously found predicates, we add all the predicates in
  // frame 1
  get_predicates(solver_, get_frame_term(1), preds, false, false, true);

  super::reset_solver();
  if (failed_to_reset_solver_) {
    throw PonoException(
        "IC3IA::reabstract Cannot reabstract because the underlying SMT solver "
        "doesn't support the reset-solver method");
  }
  predset_.clear();
  predlbls_.clear();

  // add predicates
  for (const auto & p : preds) {
    add_predicate(p);
  }
}

bool IC3IA::add_predicate(const Term & pred)
{
  if (predset_.find(pred) != predset_.end()) {
    // don't allow re-adding the same predicate
    return false;
  }

  assert(ts_.only_curr(pred));
  logger.log(2, "adding predicate {}", pred);
  predset_.insert(pred);
  assert(pred->get_sort() == boolsort_);
  assert(pred->is_symbolic_const() || is_predicate(pred, boolsort_));

  Term lbl = label(pred);
  // set the negated label as well
  // can use in either polarity because we add a bi-implication
  labels_[solver_->make_term(Not, pred)] = solver_->make_term(Not, lbl);

  predlbls_.insert(lbl);
  lbl2pred_[lbl] = pred;

  Term npred = ts_.next(pred);
  Term nlbl = label(npred);
  labels_[solver_->make_term(Not, npred)] = solver_->make_term(Not, nlbl);

  if (!pred->is_symbolic_const()) {
    // only need to assert equalities for labels that are distinct
    assert(lbl != pred);
    solver_->assert_formula(solver_->make_term(Equal, lbl, pred));
    solver_->assert_formula(solver_->make_term(Equal, nlbl, npred));

    // only need to modify transition relation for non constants
    // boolean constants will be precise

    // add predicate to abstraction and get the new constraint
    Term predabs_rel = ia_.predicate_refinement(pred);
    static_cast<RelationalTransitionSystem &>(ts_).constrain_trans(predabs_rel);
    // refine the transition relation incrementally
    // by adding a new constraint
    assert(!solver_context_);  // should be at context 0
    solver_->assert_formula(
        solver_->make_term(Implies, trans_label_, predabs_rel));
  }

  // keep track of the labels and different polarities for debugging assertions
  all_lbls_.insert(lbl);
  all_lbls_.insert(solver_->make_term(Not, lbl));
  all_lbls_.insert(nlbl);
  all_lbls_.insert(solver_->make_term(Not, nlbl));

  return true;
}

void IC3IA::register_symbol_mappings(size_t i)
{
  if (i < longest_cex_length_) {
    // these symbols should have already been handled
  }

  UnorderedTermMap & cache = to_solver_.get_cache();
  Term unrolled_sv;
  for (const auto & sv : ts_.statevars()) {
    unrolled_sv = unroller_.at_time(sv, i);
    cache[to_interpolator_.transfer_term(unrolled_sv)] = unrolled_sv;
  }
}

bool IC3IA::compute_witness() { return super::compute_witness(conc_ts_); }

}  // namespace pono
