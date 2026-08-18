# IC3IA semantic refinement packets

This experiment replaces the sparse interpolation-stall decision with a
decision at every spurious abstract counterexample handled by
`IC3IA::refine()`.

The legacy `--cegp-bandit` and `--ic3ia-fallback-preds` behavior is preserved
for reproduction.  The new controller is enabled independently:

```text
--mab-ic3ia-refinement
```

Fixed policies for oracle-gap experiments use:

```text
--ic3ia-refinement-packet 1  # LEAN_CORE
--ic3ia-refinement-packet 2  # ARRAY_LOCAL
--ic3ia-refinement-packet 3  # CEX_DIVERSE
--ic3ia-refinement-packet 4  # RECOVERY
```

Packets are:

| Packet | Contents |
| --- | --- |
| `LEAN_CORE` | Fresh sequence-interpolant predicates after core reduction |
| `ARRAY_LOCAL` | Core plus up to 8 array/important-variable candidates |
| `CEX_DIVERSE` | Core plus up to 16 CEX-support-ranked, support-diverse candidates |
| `RECOVERY` | Core plus up to 32 ranked transition candidates |

`LEAN_CORE` is masked when interpolation has no fresh predicate. Candidate
ranking is deterministic and considers overlap with the current abstract CEX,
the bad-state cone, array operations/sorts, important prophecy/history
variables, and symbol novelty. If a packet without an interpolant core cannot
rule out the current abstract trace, it is expanded deterministically; the
full fresh pool is retained as the final safe fallback.

Each selected packet receives feedback after exactly the next IC3 `step()`.
Logs use `IC3IA-REFINEMENT select`, `update`, and `censored` records. The reward
is proof progress (frame creation, propagation, frontier pushes, terminal
proof) minus solver-query, reducer-query, and predicate-count costs.

Recommended experiment order:

1. Run all four fixed policies and establish the best-fixed/oracle gap.
2. Confirm median decisions on triggered hard cases and the select/update
   ratio from telemetry.
3. Run `--mab-ic3ia-refinement` only if the fixed policies win in meaningfully
   different contexts.
4. Keep the outer CEGP controller disabled until credit assignment for this
   controller has been evaluated independently.

## Initial validation

The isolated branch was built on `bmcpu` and the full test suite passed (26/26,
LSF job `460769`). A smoke run on
`simple_array_index_value_3.btor2` proved `UNSAT` and produced four selections
and four updates (LSF job `460770`):

```text
lean_core   -> update
cex_diverse -> update
recovery    -> update
lean_core   -> terminal update
```

This is only a lifecycle and correctness smoke test. It is not a performance
claim; the fixed-policy oracle-gap experiments above are still required.

## Reports and interpretation

- `RESULTS_FULL_310.md`: 1000-second single-engine results.
- `RESULTS_FULL_310_3600.md`: 3600-second single-engine results.
- `full_310_per_case.csv` and `full_310_3600_per_case.csv`: aligned per-case
  outcomes, times, and visible packet telemetry.
- `HWMCC25_COUNT_AUDIT.md`: explains why these single-engine results must not
  be compared directly with the official 165-solved Pono portfolio result.
- `DECISION_FREQUENCY_AUDIT.md`: records the 170-case trigger coverage, median
  one decision per triggered case, cold-start limitation, and telemetry needed
  before a MathSAT factorial experiment.

The current evidence supports improved decision coverage and a reliable
selection/update lifecycle. It does not yet establish that a per-instance UCB
learns an effective policy online, because most triggered instances provide
only one decision and `ARRAY_LOCAL` is effectively invalid.
