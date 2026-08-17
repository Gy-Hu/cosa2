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

All runs use:

- `--engine ic3ia`
- `--ceg-prophecy-arrays`
- `--pseudo-init-prop`
- an effectively unbounded model-checking bound
- one CPU slot per benchmark
- a 1000 second process timeout by default

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
