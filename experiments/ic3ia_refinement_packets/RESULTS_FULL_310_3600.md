# Full Array BTOR2 results with 3600-second timeout

> **Scope correction:** these are single-engine IC3IA experiments, not the
> official HWMCC'25 Pono portfolio. The official 165-solved result uses 13
> concurrent engine configurations on a 16-core node.

Both runs use the same 310-case manifest and a 3600-second per-case timeout.

| Configuration | Solved | UNSAT | SAT | Timeout | Unknown | PAR-2 total | PAR-2 mean |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Single-engine IC3IA+CEGP control | 24/310 | 24 | 0 | 213 | 73 | 2062631.72 | 6653.65 |
| Single-engine semantic IC3IA packet MAB | 28/310 | 28 | 0 | 231 | 51 | 2036163.45 | 6568.27 |

MAB solves **+4** more cases and improves PAR-2 by
**26468.27**. On the 24
commonly solved cases, baseline/new-MAB geometric mean speedup is
**0.851x** (median **0.633x**).
There are **0** SAT/UNSAT conflicts.

## MAB newly solved versus 3600-second baseline

- `benchmarks/wordlevel/array/2019/wolf/2018A/picorv32-check-p12.btor2`: left=unknown (156.19s), right=unsat (1236.09s)
- `benchmarks/wordlevel/array/2019/wolf/2018A/picorv32-check-p20.btor2`: left=unknown (158.91s), right=unsat (666.89s)
- `benchmarks/wordlevel/array/2020/mann/array_lt200.btor2`: left=unknown (0.09s), right=unsat (0.76s)
- `benchmarks/wordlevel/array/2025/sosylab/liveness-l2s-rel/loop-crafted/simple_array_index_value_3.btor2`: left=unknown (64.25s), right=unsat (58.24s)

## MAB lost versus 3600-second baseline

- None

## Effect of increasing MAB timeout from 1000 to 3600 seconds

- Solved: 26 -> 28
- Newly solved at 3600 seconds: 2
- Lost: 0

- `benchmarks/wordlevel/array/2019/wolf/2018A/picorv32-check-p12.btor2`: left=missing (1000.22s), right=unsat (1236.09s)
- `benchmarks/wordlevel/array/2019/wolf/2019C/zipcpu_zipcpu_dcache-p581.btor2`: left=missing (1000.11s), right=unsat (2697.91s)

## Visible packet telemetry

Only the final 80 stderr lines are retained per case, so these counts are lower bounds.

| Packet | Visible selections | Visible updates |
| --- | ---: | ---: |
| `lean_core` | 277 | 270 |
| `array_local` | 0 | 0 |
| `cex_diverse` | 58 | 52 |
| `recovery` | 134 | 134 |

- Cases with visible selection: 170/310
- Visible selections: 469
- Visible updates: 456
- Visible update ratio: 97.23%
- Visible censored decisions: 0
- Aborts: 0

## Remote result directories

- MAB: `/hpc/home/connect.cchen099/gy-env/pono-array-ic3ia-mab-results-3600/8edd6c6ac17a/no_pseudo_mab_ic3ia_refinement`
- Baseline: `/hpc/home/connect.cchen099/gy-env/pono-array-baseline-results-3600-v2/d34cea4a94e9/baseline`
