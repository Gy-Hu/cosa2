# CEGP bandit experiments

This directory contains the reproducible CPU-only harness used to evaluate
learning-guided array refinement in `CegProphecyArrays<IC3IA>`.

The first experiment fixes the inner IC3IA configuration and varies only the
two post-enumeration reduction decisions.  Timed axiom reduction remains
enabled for every strategy.

| strategy | nonconsecutive reduction | consecutive reduction |
| --- | --- | --- |
| `baseline` / `full_reduce` | on | on |
| `consec_core` | off | on |
| `full_add` | off | off |
| `ucb` | selected online | selected online |
| `fallback32` | baseline | baseline, plus stalled-IC3IA recovery |
| `ucb_fallback32` | selected online | selected online, plus recovery |
| `warmup10` | baseline after BMC pre-refinement | baseline |
| `ucb_fallback32_warmup10` | selected online after BMC pre-refinement | selected online, plus recovery |

All runs use:

- `--engine ic3ia`
- `--ceg-prophecy-arrays`
- `--pseudo-init-prop`
- cvc5 as both SMT solver and interpolator (Bitwuzla returns unsupported/unknown
  on several of these UF-heavy instances)
- an effectively unbounded model-checking bound
- one CPU slot per benchmark
- a 1000 second process timeout by default

The `ucb` policy is implemented in C++ and updates only at complete
refinement/IC3 epoch boundaries. It does not use a GPU or an external ML
runtime.

The fallback variants add at most 32 previously unseen transition predicates
when sequence interpolation returns no fresh predicate. This is a sound
precision-increasing recovery from IC3IA's otherwise terminal `REFINE_FAIL`;
it is kept as a separate ablation because it is complementary to array axiom
reduction policy selection.

The warmup variant checks BMC bounds 0 through 10 before the first IC3IA
epoch. This gives safe instances an opportunity to inject useful array theory
information before IC3IA can terminate on a predicate-refinement stall.

The benchmark manifest contains the 12 HWMCC'25 word-level array
liveness-to-safety instances.  Each file has one bad property.

## Local smoke run

From the Pono repository root:

```bash
python3 experiments/cegp_bandit/run_case.py \
  --strategy baseline \
  --benchmark "$(head -n 1 experiments/cegp_bandit/liveness_2025.txt)" \
  --timeout 30 \
  --output /tmp/pono-cegp-smoke.json
```

## LSF array run

The cluster uses one-based LSF array indices.  `lsf_array.sh` converts the
index to the zero-based manifest line automatically.

```bash
experiments/cegp_bandit/submit_lsf.sh baseline 12
```

The optional second argument limits the number of simultaneously running
array elements. Results are written outside the Git worktree by default:

```text
/hpc/home/connect.cchen099/gy-env/pono-cegp-bandit-results/<commit>/<strategy>/
```

Override this location with `CEGP_RESULT_ROOT` when submitting.

## Summary

```bash
python3 experiments/cegp_bandit/summarize.py \
  /hpc/home/connect.cchen099/gy-env/pono-cegp-bandit-results/<commit>/baseline
```

PAR-2 uses twice the configured timeout for timeout, crash, and unknown runs.

Compare every completed strategy at one commit and compute the fixed-arm
oracle:

```bash
python3 experiments/cegp_bandit/compare.py \
  /hpc/home/connect.cchen099/gy-env/pono-cegp-bandit-results/<commit>
```
