# Full 310-case Array BTOR2 run: semantic IC3IA packet MAB

Run configuration:

- Branch: `research/array-ic3ia-mab`
- Algorithm commit used by the run: `ee2fd8b93138`
- Strategy: `no_pseudo_mab_ic3ia_refinement`
- Per-case timeout: 1000 seconds
- Manifest: 310 unique Array BTOR2 cases
- Result directory: `/hpc/home/connect.cchen099/gy-env/pono-array-ic3ia-mab-results-v2/ee2fd8b93138/no_pseudo_mab_ic3ia_refinement`

## Aggregate results

| Configuration | Solved | UNSAT | SAT | Timeout | Unknown | PAR-2 total | PAR-2 mean |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Original IC3IA+CEGP baseline | 23/310 | 23 | 0 | 217 | 70 | 575407.95 | 1856.15 |
| Previous no-pseudo + old UCB fallback32 | 26/310 | 26 | 0 | 235 | 49 | 569129.84 | 1835.90 |
| New no-pseudo + semantic IC3IA packet MAB | 26/310 | 26 | 0 | 236 | 48 | 569819.44 | 1838.13 |

The new semantic-packet MAB solved **26** cases. Relative to the
original baseline, the solved delta is **+3**
and PAR-2 changes by **+5588.51**
(positive means improvement). Relative to the previous full configuration, the solved delta is
**+0** and PAR-2 changes by
**-689.60**.

For commonly solved cases, the geometric mean speedup of new MAB over baseline is
**0.823x** (median **0.710x**).
There are **0** SAT/UNSAT conflicts with baseline and
**0** with the previous full configuration.

## Solved-set changes versus baseline

Newly solved:

- `benchmarks/wordlevel/array/2019/wolf/2018A/picorv32-check-p20.btor2`: baseline=unknown (149.05s), new_mab=unsat (705.76s)
- `benchmarks/wordlevel/array/2020/mann/array_lt200.btor2`: baseline=unknown (0.23s), new_mab=unsat (0.74s)
- `benchmarks/wordlevel/array/2025/sosylab/liveness-l2s-rel/loop-crafted/simple_array_index_value_3.btor2`: baseline=unknown (68.79s), new_mab=unsat (56.46s)

Lost:

- None

## Solved-set changes versus previous full configuration

Newly solved:

- None

Lost:

- None

## Visible packet telemetry

The structured result harness stores only the final 80 stderr lines per case. Therefore the
following event counts are **lower bounds**, especially for long runs with many refinement rounds.

| Packet | Visible selections | Visible updates |
| --- | ---: | ---: |
| `lean_core` | 219 | 206 |
| `array_local` | 0 | 0 |
| `cex_diverse` | 47 | 47 |
| `recovery` | 113 | 112 |

- Cases with at least one visible packet selection: **141/310**
- Visible selections: **379**
- Visible updates: **365**
- Visible selection/update ratio: **96.31%**
- Visible censored decisions: **0**

## Artifacts

- `array_ic3ia_mab_full_310_per_case.csv`: aligned per-case results and solve times for all three configurations.

The run completed all 310 unique manifest indices with no aborts. The earlier failed launch using
an ABI-stale `build/pono` binary is preserved separately and is not included in these results.
