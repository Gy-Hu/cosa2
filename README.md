# Pono-LLM4PDR: IC3/PDR with External Helper Support

## Helper Assertions, Predicates, and Clauses

Pono supports externally provided **assertions**, **predicates**, and **clauses** to accelerate IC3/PDR-based verification. These are supplied as SMT-LIB2 files containing `define-fun` declarations whose names follow a specific prefix convention.

### File Format

Each helper is a `define-fun` whose parameters match the state variable names in the BTOR2 file. For example, given a design with state variables `x` (6-bit) and `y` (6-bit):

```smt2
; Predicate — hints for abstraction refinement
(define-fun |predicate.0| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (bvult x y))

; Clause — added directly to the IC3 initial frame (F1)
(define-fun |clause.0| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (= (bvand x #b000001) (bvand y #b000001)))

; Assertion — conjoined with the property for strengthening
(define-fun |assertion.0| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
  (= (bvsub y x) (_ bv2 6)))
```

### Three Types

| Type | Name Prefix | Mechanism | Engine Support |
|------|-------------|-----------|----------------|
| **Predicate** | `predicate.` | Passed to the solver as abstraction predicates | `ic3ng-bits` |
| **Clause** | `clause.` or `f1clause.` | Validated (init-inductive) and added to frame F1 as lemmas | `ic3ng-bits` |
| **Assertion** | `assertion.` | AND-conjoined with the property; falsified assertions are automatically removed via counterexample-guided refinement | `ic3bits`, `ic3ng-bits` |

### Command-Line Usage

**Predicates** — provide abstraction hints to `ic3ng-bits`:

```bash
# simple_arithmetic benchmark with predicate helpers
./build/pono -e ic3ng-bits --promote-inputvars \
  --external-predicates benchmarks/side-load-predicate/simple_arithmetic/1.c/1_smaller.c.predicate.smt2 \
  benchmarks/side-load-predicate/simple_arithmetic/1.c/1_smaller.c.btor

# simplepipe benchmark with predicates
./build/pono -e ic3ng-bits --promote-inputvars \
  --external-predicates benchmarks/side-load-predicate/simplepipe/predicates.smt2 \
  benchmarks/side-load-predicate/simplepipe/wrapper_add_w8.btor2
```

**Clauses** — provide pre-validated lemmas for frame F1:

```bash
# xp2 benchmark with clause helpers
./build/pono -e ic3ng-bits --promote-inputvars \
  --external-clauses benchmarks/side-load-clause/xp2.helper_clauses.smt2 \
  benchmarks/side-load-clause/xp2.btor2
```

**Assertions** — strengthen the property with CEGIS-style refinement:

```bash
# two_cnt benchmark with assertion-based property strengthening (ic3ng-bits)
./build/pono -e ic3ng-bits --promote-inputvars -k 200 \
  --assertion-folder benchmarks/cegis-helper-assert/helper_assertions/ \
  benchmarks/cegis-helper-assert/simple_arithmetic/two_cnt/two_cnt.btor

# same benchmark with ic3bits engine
./build/pono -e ic3bits -k 200 \
  --assertion-folder benchmarks/cegis-helper-assert/helper_assertions/ \
  benchmarks/cegis-helper-assert/simple_arithmetic/two_cnt/two_cnt.btor
```

**All-in-one helpers** — `--external-helpers` accepts a single file containing all three prefixes, automatically categorized. Useful when an LLM generates all helpers in one shot:

```bash
# xp2 benchmark with mixed helpers (2 predicates + 2 clauses + 1 assertion)
./build/pono -e ic3ng-bits --promote-inputvars \
  --external-helpers benchmarks/side-load-clause/xp2.mixed_helpers.smt2 \
  benchmarks/side-load-clause/xp2.btor2
```

### How Assertions Work

Unlike predicates and clauses (which are sideloaded as hints), assertions use **property strengthening with refinement**:

1. All assertions are AND-conjoined with the original property: `prop' = prop ∧ a₀ ∧ a₁ ∧ ...`
2. IC3 checks the strengthened property `prop'`
3. If a counterexample is found, `refine_property` checks whether the **original property** is truly violated
4. If only some assertions are falsified, those assertions are removed and IC3 restarts with the remaining ones
5. This repeats until either the property is proved or a real counterexample is found
