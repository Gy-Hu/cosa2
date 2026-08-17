/*********************                                                  */
/*! \file cegp_bandit.h
** \brief Lightweight UCB controller for CEG prophecy array refinement.
*/

#pragma once

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <stdexcept>

namespace pono {

enum class CegpRefinementMode : size_t
{
  FULL_ADD = 0,
  CONSEC_CORE,
  FULL_REDUCE,
  NUM_MODES
};

inline const char * to_string(CegpRefinementMode mode)
{
  switch (mode) {
    case CegpRefinementMode::FULL_ADD: return "full_add";
    case CegpRefinementMode::CONSEC_CORE: return "consec_core";
    case CegpRefinementMode::FULL_REDUCE: return "full_reduce";
    case CegpRefinementMode::NUM_MODES: break;
  }
  throw std::invalid_argument("invalid CEGP refinement mode");
}

/** A deterministic, CPU-only three-arm UCB1 controller.
 *
 * Each arm is sampled once before UCB scores are used.  This keeps the policy
 * transparent and reproducible.
 */
class ThreeArmUcbController
{
 public:
  static constexpr size_t num_arms = 3;

  explicit ThreeArmUcbController(double exploration = 0.5)
      : exploration_(exploration)
  {
  }

  size_t select() const
  {
    for (size_t arm = 0; arm < num_arms; ++arm) {
      if (!counts_[arm]) {
        return arm;
      }
    }

    const double log_rounds = std::log(static_cast<double>(rounds_));
    size_t best_arm = 0;
    double best_score = score(0, log_rounds);
    for (size_t arm = 1; arm < num_arms; ++arm) {
      const double arm_score = score(arm, log_rounds);
      if (arm_score > best_score) {
        best_arm = arm;
        best_score = arm_score;
      }
    }
    return best_arm;
  }

  void update(size_t arm, double reward)
  {
    if (arm >= num_arms) {
      throw std::invalid_argument("invalid UCB arm");
    }
    counts_[arm]++;
    reward_sums_[arm] += reward;
    rounds_++;
  }

  size_t rounds() const { return rounds_; }
  size_t count(size_t arm) const { return counts_.at(arm); }
  double mean_reward(size_t arm) const
  {
    return counts_.at(arm) ? reward_sums_.at(arm) / counts_.at(arm) : 0.0;
  }

 private:
  double score(size_t arm, double log_rounds) const
  {
    const double count = static_cast<double>(counts_[arm]);
    const double mean = reward_sums_[arm] / count;
    return mean + exploration_ * std::sqrt(2.0 * log_rounds / count);
  }

  double exploration_;
  size_t rounds_ = 0;
  std::array<size_t, num_arms> counts_{};
  std::array<double, num_arms> reward_sums_{};
};

enum class IC3IARefinementPacket : size_t
{
  LEAN_CORE = 0,
  ARRAY_LOCAL,
  CEX_DIVERSE,
  RECOVERY,
  NUM_PACKETS
};

inline const char * to_string(IC3IARefinementPacket packet)
{
  switch (packet) {
    case IC3IARefinementPacket::LEAN_CORE: return "lean_core";
    case IC3IARefinementPacket::ARRAY_LOCAL: return "array_local";
    case IC3IARefinementPacket::CEX_DIVERSE: return "cex_diverse";
    case IC3IARefinementPacket::RECOVERY: return "recovery";
    case IC3IARefinementPacket::NUM_PACKETS: break;
  }
  throw std::invalid_argument("invalid IC3IA refinement packet");
}

/** Four-arm UCB1 controller with action masking.
 *
 * IC3IA cannot use LEAN_CORE when sequence interpolation produced no fresh
 * predicate.  Masking invalid actions avoids treating an empty packet as a
 * real refinement decision.
 */
class IC3IARefinementUcbController
{
 public:
  static constexpr size_t num_arms =
      static_cast<size_t>(IC3IARefinementPacket::NUM_PACKETS);

  explicit IC3IARefinementUcbController(double exploration = 0.5)
      : exploration_(exploration)
  {
  }

  IC3IARefinementPacket select(const std::array<bool, num_arms> & valid) const
  {
    bool any_valid = false;
    for (size_t arm = 0; arm < num_arms; ++arm) {
      if (!valid[arm]) {
        continue;
      }
      any_valid = true;
      if (!counts_[arm]) {
        return static_cast<IC3IARefinementPacket>(arm);
      }
    }
    if (!any_valid) {
      throw std::invalid_argument("no valid IC3IA refinement packet");
    }

    const double log_rounds =
        std::log(static_cast<double>(std::max<size_t>(1, rounds_)));
    size_t best_arm = num_arms;
    double best_score = 0.0;
    for (size_t arm = 0; arm < num_arms; ++arm) {
      if (!valid[arm]) {
        continue;
      }
      const double arm_score = score(arm, log_rounds);
      if (best_arm == num_arms || arm_score > best_score) {
        best_arm = arm;
        best_score = arm_score;
      }
    }
    return static_cast<IC3IARefinementPacket>(best_arm);
  }

  void update(IC3IARefinementPacket packet, double reward)
  {
    const size_t arm = static_cast<size_t>(packet);
    if (arm >= num_arms) {
      throw std::invalid_argument("invalid IC3IA refinement packet");
    }
    counts_[arm]++;
    reward_sums_[arm] += reward;
    rounds_++;
  }

  size_t rounds() const { return rounds_; }
  size_t count(IC3IARefinementPacket packet) const
  {
    return counts_.at(static_cast<size_t>(packet));
  }
  double mean_reward(IC3IARefinementPacket packet) const
  {
    const size_t arm = static_cast<size_t>(packet);
    return counts_.at(arm) ? reward_sums_.at(arm) / counts_.at(arm) : 0.0;
  }

 private:
  double score(size_t arm, double log_rounds) const
  {
    const double count = static_cast<double>(counts_[arm]);
    return reward_sums_[arm] / count
           + exploration_ * std::sqrt(2.0 * log_rounds / count);
  }

  double exploration_;
  size_t rounds_ = 0;
  std::array<size_t, num_arms> counts_{};
  std::array<double, num_arms> reward_sums_{};
};

/** Typed wrapper for CEG prophecy refinement modes. */
class CegpUcbController
{
 public:
  explicit CegpUcbController(double exploration = 0.5)
      : controller_(exploration)
  {
  }

  CegpRefinementMode select() const
  {
    return static_cast<CegpRefinementMode>(controller_.select());
  }

  void update(CegpRefinementMode mode, double reward)
  {
    controller_.update(static_cast<size_t>(mode), reward);
  }

  size_t rounds() const { return controller_.rounds(); }
  size_t count(CegpRefinementMode mode) const
  {
    return controller_.count(static_cast<size_t>(mode));
  }
  double mean_reward(CegpRefinementMode mode) const
  {
    return controller_.mean_reward(static_cast<size_t>(mode));
  }

 private:
  ThreeArmUcbController controller_;
};

}  // namespace pono
