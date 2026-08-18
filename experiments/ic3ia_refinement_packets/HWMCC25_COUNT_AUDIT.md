# Why the local 24/28 counts do not match HWMCC'25 Pono's 165

## Conclusion

The benchmark archive and 310-case manifest are correct. The mismatch comes
from running a different solver configuration and calling it a Pono baseline.

The HWMCC'25 `pono` entry is a 13-process portfolio submitted from Pono's
`hwmcc25` tag. The local experiments run one IC3IA process with CVC5 on one CPU
slot. They are valid single-engine IC3IA A/B experiments, but they are not a
reproduction of the official Pono entry and must not be compared directly with
165 solved.

## Benchmark identity is correct

- Server archive MD5: `8e22de719add33658e5816621c625ad8`.
- Zenodo archive MD5: `8e22de719add33658e5816621c625ad8`.
- Archive BTOR2 files: 310.
- Manifest entries: 310 unique paths.
- Year split, both locally and in the official CSV: 2019=64, 2020=6,
  2024=120, 2025=120.

Therefore no benchmark was omitted or duplicated.

## What the official result means

The official HWMCC'25 Word-Level Arrays CSV contains 310 Pono rows:

- 55 `sat`
- 110 `unsat`
- 145 unsolved (`none`)
- 165 solved in total

The HWMCC page reports the same certified and uncertified total.

Official sources:

- [HWMCC'25 results](https://hwmcc.github.io/2025/)
- [Zenodo benchmark and raw-result artifact](https://zenodo.org/records/17428464)
- [Official Pono array portfolio at tag `hwmcc25`](https://github.com/stanford-centaur/pono/blob/hwmcc25/scripts/parallel_pono_array.py)

## Official Pono is a 13-engine portfolio

The submitted `parallel_pono_array.py` launches these configurations
concurrently and returns when the first one solves the benchmark:

1. BMC with static COI and exponential bounds
2. K-induction
3. K-induction with BV arithmetic CEGAR
4. K-induction with BV arithmetic CEGAR and no simple-path check
5. Forward interpolation
6. Backward interpolation
7. Eager-unroll interpolation
8. Interpolation with BV arithmetic CEGAR
9. Backward interpolation with BV arithmetic CEGAR
10. ISMC
11. ISMC with BV arithmetic CEGAR
12. IC3IA+CEGP with MathSAT
13. IC3IA+CEGP with MathSAT and BV arithmetic CEGAR

Competition hardware gave each checker a full 16-physical-core node and
120 GB memory for one hour. Across officially solved Pono rows, the mean
CPU-time/wall-time ratio is 12.83, consistent with the 13 concurrent engines.

## What the local experiments actually ran

Every local case executes only:

```text
build/pono
  --engine ic3ia
  --ceg-prophecy-arrays
  --smt-solver cvc5
  --smt-interpolator cvc5
  --bound 2147483646
```

The control adds `--pseudo-init-prop`; the new MAB configuration disables
pseudo-init and adds `--mab-ic3ia-refinement`.

Each LSF case requests one CPU slot. For locally solved cases, mean
CPU-time/wall-time is 0.98 for the control and 0.97 for MAB, confirming that
they are effectively single-core runs. The current build is not compiled with
MathSAT and has no MathSAT library linked, so it cannot execute the official
IC3IA sub-configuration either.

## Why all 55 official SAT results disappeared

The official portfolio contains an explicit BMC configuration optimized for
counterexample discovery. The local single-IC3IA runs contain no BMC race and
solve zero SAT cases:

| Result class | Official Pono | Local IC3IA control | Local IC3IA MAB |
| --- | ---: | ---: | ---: |
| SAT | 55 | 0 | 0 |
| UNSAT | 110 | 24 | 28 |
| Total | 165 | 24 | 28 |

Examples:

- `picorv32_mutAX_mem-p0`: official Pono SAT in 170.54 s; both local runs
  time out at 3600 s.
- `rocket_2029`: official Pono SAT in 536.87 s; both local runs time out.
- `riscv_formal_nerv_axi_cache_bus_imem_ch0_faulty-p2`: official Pono SAT in
  55.77 s; both local runs time out.

The zero-SAT outcome is therefore a configuration effect, not a result parser
or manifest error.

## Source-version mismatch

The official submission tag points to commit
`04d8e871abcfaae08975038a47a9c007f0c9fb2b`. The research work started from
Pono main commit `d5dea72a38a292fd06e32caa02f16626e4e859fc` plus research commits.
The official tag is not an ancestor of that main commit; their merge base is
`74fddc7ef7d177a91b657eb2d2fd91e22b32e610`. The portfolio scripts and engine
code differ materially.

## Correct interpretation and next experiment

Rename the existing configurations conceptually as:

- `IC3IA single-engine control`
- `IC3IA semantic-packet MAB`

Their 24-vs-28 result measures the complete single-engine configurations; it
does not reproduce or beat official Pono.

A competition-level comparison requires:

1. branch from the `hwmcc25` tag;
2. port the MAB IC3IA change to that version;
3. build with MathSAT;
4. run the official 13-engine array portfolio;
5. allocate approximately 13 CPU slots and competition-comparable memory per
   case;
6. compare official portfolio vs the same portfolio with only the IC3IA member
   changed.

For isolating the research contribution, a second experiment should compare
the official MathSAT IC3IA member alone against the modified MathSAT IC3IA
member, with identical options and resources.
