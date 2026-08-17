# Full HWMCC'25 word-level array results

- Date: 2026-08-17
- Cluster: IBM Spectrum LSF `bmcpu`
- Benchmark: every `.btor2` file in `benchmarks/wordlevel/array`
- Cases: 310 files, each containing exactly one `bad` property
- Per-instance timeout: 1000 seconds
- PAR-2 timeout/unknown/error penalty: 2000 seconds
- Manifest SHA-256: `4819b58261a85169452b4402b77fd332debc1e5ae8e2297efbfc35038e44b8f0`

## Main result

| Configuration | Solved | UNSAT | Timeout | Unknown | PAR-2 total | PAR-2 mean |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| IC3IA+CEGP baseline | 23/310 | 23 | 217 | 70 | 575407.95 | 1856.15 |
| No-pseudo + fallback UCB32 | **26/310** | **26** | 235 | 49 | **569129.84** | **1835.90** |

Relative to the baseline, the final CPU-only UCB configuration:

- solves 3 additional instances;
- loses 0 baseline-solved instances;
- improves total PAR-2 by 6278.11;
- improves mean PAR-2 by 20.25;
- produces no SAT/UNSAT conflicts.

## Results by benchmark year

| Year | Cases | Baseline solved | UCB solved | Baseline PAR-2 | UCB PAR-2 |
| --- | ---: | ---: | ---: | ---: | ---: |
| 2019 | 64 | 19 | 20 | 91401.65 | 89070.02 |
| 2020 | 6 | 0 | 1 | 12000.00 | 10000.93 |
| 2024 | 120 | 1 | 1 | 238003.34 | 238004.19 |
| 2025 | 120 | 3 | 4 | 234002.96 | 232054.70 |

## Newly solved instances

```text
benchmarks/wordlevel/array/2019/wolf/2018A/
picorv32-check-p20.btor2

benchmarks/wordlevel/array/2020/mann/
array_lt200.btor2

benchmarks/wordlevel/array/2025/sosylab/liveness-l2s-rel/loop-crafted/
simple_array_index_value_3.btor2
```

Every newly solved result is `UNSAT`. There are no instances solved by the
baseline and lost by the final configuration.

## Configuration

The baseline command uses cvc5 for solving/interpolation, pseudo-init/property,
and the original CEGP reduction defaults:

```bash
./build/pono \
  --engine ic3ia \
  --bound 2147483646 \
  --smt-solver cvc5 \
  --smt-interpolator cvc5 \
  --pseudo-init-prop \
  --ceg-prophecy-arrays \
  <benchmark.btor2>
```

The final configuration removes pseudo-init/property and enables both online
UCB control and the sound transition-predicate fallback:

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

The core final code is commit:

```text
80f5493 ic3ia: credit fallback actions over complete epochs
```

## Reproduction and raw results

The deterministic manifest is:

```text
/hpc/home/connect.cchen099/gy-env/pono-cegp-bandit-manifests/
all-array-310.txt
```

Raw JSON results are under:

```text
/hpc/home/connect.cchen099/gy-env/pono-cegp-bandit-results/
29de180e1f45/baseline/

/hpc/home/connect.cchen099/gy-env/pono-cegp-bandit-results/
29de180e1f45/no_pseudo_ucb_fallback32/
```

LSF job arrays:

| Manifest indices | Baseline job | Final UCB job |
| --- | ---: | ---: |
| 1–64 | 460310 | 460330 |
| 65–128 | 460354 | 460355 |
| 129–192 | 460419 | 460420 |
| 193–256 | 460478 | 460479 |
| 257–310 | 460528 | 460529 |

The experiment harness commits after the core implementation add deterministic
manifest generation, range-sharded submission, and pipelined LSF orchestration.

## Completion audit

- Both strategies have exactly 310 unique JSON records.
- Both record sets exactly equal the 310-line manifest.
- The manifest covers 64 files from 2019, 6 from 2020, 120 from 2024, and 120
  from 2025.
- Every BTOR2 file has exactly one `bad` property.
- All 26 Pono repository tests pass after the final C++ changes.
- No full-track research jobs remain active.

## Interpretation

The requested full-track performance target is met: the final configuration
solves more instances and has lower PAR-2 than the single baseline run.

The comparison is between complete configurations, not a claim that UCB alone
accounts for the entire gain. The final configuration combines removal of the
optional pseudo-init/property transformation, transition-predicate recovery
when IC3IA interpolation stalls, and online UCB selection of fallback strength.
The earlier 12-case ablations in `RESULTS.md` show that removing pseudo-init
alone still solved 0/12, while adding fallback/UCB produced the new solved
liveness instance.
