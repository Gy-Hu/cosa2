#include <tuple>

#include "core/prop.h"
#include "core/rts.h"
#include "gtest/gtest.h"
#include "options/options.h"
#include "smt-switch/smt.h"
#include "smt/available_solvers.h"
#include "utils/cegp_bandit.h"
#include "utils/make_provers.h"

using namespace pono;
using namespace smt;
using namespace std;

namespace pono_tests {

TEST(CegpBanditTest, ExploreThenExploit)
{
  CegpUcbController controller(0.0);

  ASSERT_EQ(controller.select(), CegpRefinementMode::FULL_ADD);
  controller.update(CegpRefinementMode::FULL_ADD, 0.1);
  ASSERT_EQ(controller.select(), CegpRefinementMode::CONSEC_CORE);
  controller.update(CegpRefinementMode::CONSEC_CORE, 0.9);
  ASSERT_EQ(controller.select(), CegpRefinementMode::FULL_REDUCE);
  controller.update(CegpRefinementMode::FULL_REDUCE, 0.2);

  ASSERT_EQ(controller.rounds(), 3);
  ASSERT_EQ(controller.select(), CegpRefinementMode::CONSEC_CORE);
  ASSERT_EQ(controller.count(CegpRefinementMode::CONSEC_CORE), 1);
  ASSERT_DOUBLE_EQ(controller.mean_reward(CegpRefinementMode::CONSEC_CORE),
                   0.9);
}

TEST(IC3IARefinementBanditTest, MasksInvalidPackets)
{
  IC3IARefinementUcbController controller(0.0);
  array<bool, IC3IARefinementUcbController::num_arms> valid{};
  valid[static_cast<size_t>(IC3IARefinementPacket::ARRAY_LOCAL)] = true;
  valid[static_cast<size_t>(IC3IARefinementPacket::CEX_DIVERSE)] = true;
  valid[static_cast<size_t>(IC3IARefinementPacket::RECOVERY)] = true;

  ASSERT_EQ(controller.select(valid), IC3IARefinementPacket::ARRAY_LOCAL);
  controller.update(IC3IARefinementPacket::ARRAY_LOCAL, 0.1);
  ASSERT_EQ(controller.select(valid), IC3IARefinementPacket::CEX_DIVERSE);
  controller.update(IC3IARefinementPacket::CEX_DIVERSE, 0.9);
  ASSERT_EQ(controller.select(valid), IC3IARefinementPacket::RECOVERY);
  controller.update(IC3IARefinementPacket::RECOVERY, 0.2);

  ASSERT_EQ(controller.select(valid), IC3IARefinementPacket::CEX_DIVERSE);
  ASSERT_EQ(controller.count(IC3IARefinementPacket::LEAN_CORE), 0);
}

TEST(IC3IARefinementBanditTest, RejectsEmptyMask)
{
  IC3IARefinementUcbController controller;
  array<bool, IC3IARefinementUcbController::num_arms> valid{};
  ASSERT_THROW(controller.select(valid), invalid_argument);
}

class CegProphecyArraysTest
    : public ::testing::TestWithParam<tuple<SolverEnum, SolverEnum>>
{
 protected:
  void SetUp() override
  {
    opts.smt_solver_ = get<0>(GetParam());
    opts.smt_interpolator_ = get<1>(GetParam());
    s = create_solver(opts.smt_solver_);
    s->set_opt("produce-unsat-assumptions", "true");
  }
  PonoOptions opts;
  SmtSolver s;
};

TEST_P(CegProphecyArraysTest, Simple)
{
  RelationalTransitionSystem rts(s);
  Sort intsort = rts.make_sort(INT);
  Sort arrsort = rts.make_sort(ARRAY, intsort, intsort);
  Term i = rts.make_statevar("i", intsort);
  Term j = rts.make_statevar("j", intsort);
  Term d = rts.make_statevar("d", intsort);
  Term a = rts.make_statevar("a", arrsort);

  Term constarr0 = rts.make_term(rts.make_term(0, intsort), arrsort);
  rts.set_init(rts.make_term(Equal, a, constarr0));
  rts.assign_next(
      a,
      rts.make_term(Ite,
                    rts.make_term(Lt, d, rts.make_term(200, intsort)),
                    rts.make_term(Store, a, i, d),
                    a));

  Term prop_term = rts.make_term(
      Lt, rts.make_term(Select, a, j), rts.make_term(200, intsort));
  SafetyProperty prop(s, prop_term);
  std::shared_ptr<SafetyProver> cegp =
      make_ceg_proph_prover(INTERP, prop, rts, s, opts);
  ProverResult r = cegp->check_until(5);
  ASSERT_EQ(r, ProverResult::TRUE);
}

TEST_P(CegProphecyArraysTest, SimpleBanditIC3IA)
{
  RelationalTransitionSystem rts(s);
  Sort intsort = rts.make_sort(INT);
  Sort arrsort = rts.make_sort(ARRAY, intsort, intsort);
  Term i = rts.make_statevar("i", intsort);
  Term j = rts.make_statevar("j", intsort);
  Term d = rts.make_statevar("d", intsort);
  Term a = rts.make_statevar("a", arrsort);

  Term constarr0 = rts.make_term(rts.make_term(0, intsort), arrsort);
  rts.set_init(rts.make_term(Equal, a, constarr0));
  rts.assign_next(
      a,
      rts.make_term(Ite,
                    rts.make_term(Lt, d, rts.make_term(200, intsort)),
                    rts.make_term(Store, a, i, d),
                    a));

  Term prop_term = rts.make_term(
      Lt, rts.make_term(Select, a, j), rts.make_term(200, intsort));
  SafetyProperty prop(s, prop_term);
  opts.cegp_bandit_ = true;
  std::shared_ptr<SafetyProver> cegp =
      make_ceg_proph_prover(IC3IA_ENGINE, prop, rts, s, opts);
  ProverResult r = cegp->check_until(5);
  ASSERT_EQ(r, ProverResult::TRUE);
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedCegProphecyArraysTest,
    CegProphecyArraysTest,
    testing::Combine(
        testing::ValuesIn(filter_solver_enums({ THEORY_INT })),
        testing::ValuesIn(filter_interpolator_enums({ THEORY_INT }))));

}  // namespace pono_tests
