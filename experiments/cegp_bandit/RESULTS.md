# HWMCC'25 array liveness results

- Date: 2026-08-17
- Cluster: IBM Spectrum LSF `bmcpu`
- Benchmark: all 12 HWMCC'25 word-level array liveness-to-safety instances
- Per-instance timeout: 1000 seconds
- PAR-2 timeout penalty: 2000 seconds

## Main result

| Configuration | Solved | SAT | UNSAT | Timeouts | PAR-2 total | PAR-2 mean |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| IC3IA+CEGP baseline | 0/12 | 0 | 0 | 8 | 24000.00 | 2000.00 |
| Baseline without pseudo-init/property | 0/12 | 0 | 0 | 7 | 24000.00 | 2000.00 |
| No-pseudo + fixed fallback32 | 1/12 | 0 | 1 | 9 | 22049.28 | 1837.44 |
| No-pseudo + fallback UCB32 | **1/12** | 0 | 1 | 9 | **22048.32** | **1837.36** |

Relative to the baseline, the final UCB configuration solves one additional
instance, improves total PAR-2 by 1951.68, and improves mean PAR-2 by 162.64.

The solved instance is:

```text
benchmarks/wordlevel/array/2025/sosylab/liveness-l2s-rel/
loop-crafted/simple_array_index_value_3.btor2
```

It is proved `unsat` in 48.32 seconds by the final configuration. The baseline
returns `unknown` on this instance and therefore receives the 2000 second
PAR-2 penalty.

## Reproduction

Final GitHub-sanitized code commit:

```text
1c13aba9e372 ic3ia: credit fallback actions over complete epochs
```

Final command shape:

```bash
./build/pono \
  --engine ic3ia \
  --bound 2147483646 \
  --smt-solver cvc5 \
  --smt-interpolator cvc5 \
  --ceg-prophecy-arrays \
  --cegp-bandit \
  --ic3ia-fallback-preds 32 \
  <benchmark.btor2>
```

Submit the full LSF array with:

```bash
CEGP_TIMEOUT=1000 \
  experiments/cegp_bandit/submit_lsf.sh no_pseudo_ucb_fallback32 12
```

Important result directories:

```text
# baseline, LSF job 460228
/hpc/home/connect.cchen099/gy-env/pono-cegp-bandit-results/
554c28502443/baseline/

# no-pseudo ablation, LSF job 460275
/hpc/home/connect.cchen099/gy-env/pono-cegp-bandit-results/
479f0a2b5656/no_pseudo/

# fixed fallback ablation, LSF job 460258
/hpc/home/connect.cchen099/gy-env/pono-cegp-bandit-results/
3db26dc72d35/no_pseudo_fallback32/

# final UCB, LSF job 460283
/hpc/home/connect.cchen099/gy-env/pono-cegp-bandit-results/
80f549363357/no_pseudo_ucb_fallback32/
```

The directory prefixes above are original cluster experiment IDs. Publication
commit IDs are listed in `PUBLISH_COMMIT_MAP.md`.

## Learning telemetry

On the solved instance, the final controller recorded:

```text
IC3IA-FALLBACK-BANDIT select round=0 arm=0 limit=32 candidates=18
IC3IA-FALLBACK-BANDIT update round=1 arm=0 reward=0.540625 \
  push=15/64 frontier=15 frames=4 result=1
```

On `reducercommutativity/max.btor2`, it exercised all three fallback strengths
over five rounds:

```text
round 0: arm 0, limit 32, 92 candidates, reward 0.37194
round 1: arm 1, limit 16, 60 candidates, reward 0
round 2: arm 2, limit 8, 44 candidates, reward 0
round 3: arm 0, limit 32, 36 candidates, reward 0
round 4: arm 1, limit 16, 4 candidates, reward 0
```

This confirms that the learning code performs online actions and updates on
the target liveness workload, rather than only compiling or running in a unit
test.

## Ablations and negative results

- The original `FULL_REDUCE`, `CONSEC_CORE`, `FULL_ADD`, and outer CEGP UCB
  configurations all solve 0/12 with mean PAR-2 2000. No outer array-refinement
  action occurs before IC3IA stalls on these instances.
- Disabling pseudo-init/property alone still solves 0/12. The transition-
  predicate fallback is necessary for the new solved instance.
- cvc5 as the main solver with Bitwuzla interpolation solves 0/12 for each of
  the tested fixed/fallback/UCB configurations.
- BMC warmup through bound 10 finds zero array axioms on the inspected
  liveness cases and creates no UCB action opportunity. The remaining warmup
  jobs were stopped after this negative result; the code remains default-off
  so the experiment is reproducible.
- Bitwuzla as the main solver is unsuitable for the full set: several cases
  terminate on unsupported UF equality or invalid UNSAT-assumption queries.

## Interpretation and limitation

The performance target against baseline is met. However, the final UCB result
does not establish a statistically meaningful advantage over the fixed
fallback32 ablation: both solve the same one instance and their approximately
one-second difference is within normal run-to-run noise. The current benchmark
offers few array-refinement/fallback decisions per process, so a stronger
learning claim requires either more training instances, warm-started priors,
or a richer contextual decision point.

All 26 repository tests pass after the final C++ changes.
