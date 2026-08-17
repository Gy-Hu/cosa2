# Exported CEGP/IC3IA experiments

This directory contains all structured experiment results and a compressed
archive of the complete LSF/diagnostic artifacts.

Commit-like directory names and the `result_commit` CSV column use the original
cluster experiment IDs. Their GitHub-sanitized commit equivalents are listed
in `../PUBLISH_COMMIT_MAP.md`.

## Full 310-case result

| Configuration | Solved | PAR-2 total | PAR-2 mean |
| --- | ---: | ---: | ---: |
| IC3IA+CEGP baseline | 23/310 | 575407.95 | 1856.15 |
| Final CPU-only UCB | **26/310** | **569129.84** | **1835.90** |

- Solved delta: **+3**
- Total PAR-2 improvement: **6278.11**
- Lost baseline-solved cases: **0**
- SAT/UNSAT conflicts: **0**

Newly solved cases:

- `benchmarks/wordlevel/array/2019/wolf/2018A/picorv32-check-p20.btor2`
- `benchmarks/wordlevel/array/2020/mann/array_lt200.btor2`
- `benchmarks/wordlevel/array/2025/sosylab/liveness-l2s-rel/loop-crafted/simple_array_index_value_3.btor2`

## MAB trigger frequency

MAB activity is sparse on this benchmark set:

| Measurement | Value |
| --- | ---: |
| Cases with any MAB selection | 23/310 (7.42%) |
| Cases with outer CEGP arm selection | 1/310 (0.32%) |
| Cases with IC3IA fallback arm selection | 22/310 (7.10%) |
| Total MAB selections | 34 |
| Total MAB updates | 18 |
| Fallback arm-0 selections | 25 |
| Fallback arm-1 selections | 5 |
| Fallback arm-2 selections | 3 |

Most instances never reach either learning decision point. The performance
comparison is therefore between complete configurations; it is not evidence
that MAB alone explains the full gain.

## Files

- `full_310_per_case.csv`: all 310 baseline/final outcomes and solve times.
- `mab_events_per_case.csv`: per-case MAB selections, arms, limits, and rewards.
- `run_summary.csv`: every recorded commit/strategy experiment, including
  partial or cancelled ablations.
- `raw_json/`: all 810 structured case JSON files.
- `raw_experiment_artifacts.tar.gz`: all raw result directories, LSF logs, diagnostic logs, and
  the validated manifest (236910 bytes).
- `SHA256SUMS`: archive integrity hash.
