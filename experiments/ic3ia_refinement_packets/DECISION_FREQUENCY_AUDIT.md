# IC3IA MAB decision-frequency audit

## Scope

This audit uses the 310-case, 3600-second single-engine semantic-packet MAB
run. The harness retains only the final 80 stderr lines per case, so event
counts are lower bounds. They are nevertheless sufficient to expose the
per-instance cold-start problem.

## Where the decision actually occurs

`IC3Base::check_until()` calls `IC3IA::refine()` only after an IC3 `step()`
returns an abstract counterexample. The MAB selection is later still:

```text
IC3 step returns FALSE
  -> IC3IA::refine() enters
  -> build unrolled trace
  -> sequence interpolation
  -> extract fresh interpolant predicates
  -> build and mask candidate packets
  -> MAB selection
```

A case can therefore have no selection because it is proved from the initial
predicate abstraction, remains inside an IC3 step until timeout, remains in
outer CEGP work, times out during interpolation, produces a concrete trace, or
has no valid packet choice. The current telemetry does not log phase entry and
cannot distinguish all of these paths.

## Observed 3600-second breakdown

| Outcome | Visible decision | No visible decision |
| --- | ---: | ---: |
| UNSAT | 5 | 23 |
| UNKNOWN | 51 | 0 |
| Timeout | 114 | 117 |
| Total | 170 | 140 |

The 23 UNSAT cases without a decision were proved without semantic packet
selection. The 117 no-decision timeouts are the main unresolved group.

Among the 170 cases with a visible learning decision:

| Visible decisions per case | Cases |
| --- | ---: |
| 1 | 91 |
| 2 | 25 |
| 3 | 28 |
| 4 or more | 26 |

- Median decisions per triggered case: 1
- Mean: 2.76
- Maximum visible decisions: 24
- Total visible selections: 469
- Total visible updates: 456
- Visible selection/update ratio: 97.23%

All visible selections were logged with `learning=true`; they had at least two
valid actions. However, 91/170 triggered cases had only one decision, so a
controller initialized independently for every benchmark usually cannot move
beyond its first exploratory action. Aggregate event count is therefore a
misleading proxy for within-instance learning.

## Arm validity

Visible selections in the same run were:

| Packet | Selections |
| --- | ---: |
| `LEAN_CORE` | 277 |
| `ARRAY_LOCAL` | 0 |
| `CEX_DIVERSE` | 58 |
| `RECOVERY` | 134 |

Most decisions had two or three valid actions. Only one visible decision had
all four actions valid. Array provenance is largely lost after abstraction,
so `ARRAY_LOCAL` is not currently a meaningful arm.

## Interpretation

Moving the decision from outer CEGP to `IC3IA::refine()` materially improves
coverage relative to the old controller (23 cases, 34 selections, 18 updates),
but it does not make per-instance cold-start UCB reliable. The new location is
semantically appropriate for predicate refinement; the learning model still
needs either a trained cross-instance prior or a higher-frequency decision
object.

The current result supports the statement:

> IC3IA refinement provides substantially more attributable decisions than
> outer CEGP refinement.

It does not yet support:

> A UCB controller learns an effective policy online from scratch within most
> individual benchmarks.

## Required telemetry before the MathSAT factorial experiment

Persist full JSONL events, rather than only stderr tails:

```text
ic3_step_start / ic3_step_end
ic3ia_refine_enter
interpolation_start / interpolation_end
candidate_pool_built
valid_action_count
mab_select / mab_update
array_reabstract / bv_reabstract
censored
```

This will separate no-decision timeouts into IC3-step, outer-CEGP,
interpolation, and no-choice categories.

## Recommended policy design

1. Keep the predicate-packet decision in `IC3IA::refine()`.
2. Restore semantic array provenance so `ARRAY_LOCAL` is valid.
3. Compare fixed packets to establish an oracle gap.
4. Train a prior on disjoint benchmark families and freeze it for test cases.
5. Permit small within-instance updates from that prior.
6. Treat an `IC3Base::inductive_generalization()` controller as a separate,
   genuinely high-frequency research route.

The proposed MathSAT 2x2 comparison remains meaningful as a system-level
experiment:

```text
IC3IA+CEGP+MathSAT
IC3IA+CEGP+MathSAT+BV-arithmetic CEGAR
IC3IA+CEGP+MathSAT+MAB
IC3IA+CEGP+MathSAT+BV-arithmetic CEGAR+MAB
```

All four groups must keep pseudo-init, solver, interpolator, bound, resources,
and reduction options identical. This factorial design measures MAB's main
effect and its interaction with the outer BV-arithmetic CEGAR loop, but fixed
packet controls are still required to attribute any gain specifically to
online learning.
