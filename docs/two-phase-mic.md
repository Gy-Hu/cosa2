# Two-Phase Hierarchical MIC for Helper Predicate Generalization

## Problem

Helper predicates loaded via `--external-predicates` were silently dropped during IC3's inductive generalization (MIC), making them ineffective.

**Root causes:**

1. **Partial cex assignment.** `get_min_pred` produces bit-level partial cubes (e.g., only `bit1(x)=1` out of 6 bits). `extend_predicates` previously used `get_value` to evaluate predicates under this partial model, adding predicates not actually implied by the cex.

2. **MIC drops all predicates.** The standard MIC loop calls `ic3_down`, which extracts an UNSAT core from the assumptions. The solver finds a minimal core using only 1-2 bit-level assignments, so all word-level predicates are dropped as redundant.

## Solution: Two-Phase MIC

Inspired by Hierarchical Delta Debugging and IC3 with Implicit Predicate Abstraction.

**Phase 1 — Freeze predicates, minimize bits only:**
- Helper predicate next-state terms are hard-asserted (not passed as assumptions) in `ic3_down`'s inductiveness check.
- UNSAT core extraction can only remove bit-level assignments.
- Predicates "catalyze" bit removal: their constraints make bit-level assignments redundant.
- Outer MIC loop skips removal attempts on helper predicates.

**Phase 2 — Selectively drop redundant predicates:**
- After Phase 1 produces (all predicates + minimal bits), iterate through each predicate.
- Tentatively remove it; check if the cube remains inductive and disjoint from init.
- If yes → predicate is redundant, drop it.
- If no → predicate is essential, keep it.
- Interaction effects are handled naturally: dropping pred A may make pred B essential.

Note: Phase 2 is order-sensitive. Two predicates that each independently maintain inductiveness will keep whichever appears later in the list.

## Key files changed

- `engines/ic3ng-support/predload.cpp` — Restored `check_sat_assuming` in `extend_predicates` (fixes partial-cex bug).
- `engines/ic3ng-support/indgen.cpp` — Two-phase MIC in `inductive_generalization_mic`; hard-assert helper preds in `ic3_down`.
- `engines/ic3ng.h` — Added `npred` parameter to `ic3_down`.
- `deps/smt-switch/include/solver.h` — Added `simplify_term` virtual method.
- `deps/smt-switch/bitwuzla/` — Bitwuzla `simplify_term` implementation.

## Benchmark results (xp2)

Circuit: two 6-bit counters, `x` starts at 0, `y` at 2, both increment until `x=61`. Property: `x < y`.

| # | Configuration | Result | Time | Frames | Lemmas generated |
|---|---|---|---|---|---|
| 1 | No helpers | **timeout** | >120s | >F8, growing | >27, size increasing |
| 2 | Predicate only | `unsat` | 0.03s | F3 fixpoint | 4 (word-level, size 1-3) |
| 3 | Clause only | `unsat` | 0.01s | F2 fixpoint | 0 (clauses injected to F1) |
| 4 | Assertion only | `unsat` | 0.01s | F1 | 0 (property strengthened) |
| 5 | Mixed (all three) | `unsat` | 0.01s | F1 | 0 |

## Reproduce

```bash
# Build
cd build && make all -j$(nproc)

# 1. Baseline (no helpers) — times out
timeout 120 ./build/pono -e ic3ng-bits --promote-inputvars -k 200 samples/xp2.btor2

# 2. Predicate only
./build/pono -e ic3ng-bits --promote-inputvars -k 200 \
  --external-predicates samples/xp2.helper.smt2 samples/xp2.btor2

# 3. Clause only
./build/pono -e ic3ng-bits --promote-inputvars -k 200 \
  --external-clauses benchmarks/side-load-clause/xp2.helper_clauses.smt2 \
  benchmarks/side-load-clause/xp2.btor2

# 4. Assertion only
./build/pono -e ic3ng-bits --promote-inputvars -k 200 \
  --external-assertions samples/xp2.assertion.smt2 samples/xp2.btor2

# 5. Mixed (pred + clause + assertion)
./build/pono -e ic3ng-bits --promote-inputvars -k 200 \
  --external-helpers benchmarks/side-load-clause/xp2.mixed_helpers.smt2 \
  benchmarks/side-load-clause/xp2.btor2

# Verbose output (shows Phase 1/2 details)
./build/pono -e ic3ng-bits --promote-inputvars -k 200 -v 1 \
  --external-predicates samples/xp2.helper.smt2 samples/xp2.btor2 \
  2>&1 | grep -E "\[ig-mic\] Phase"
```
