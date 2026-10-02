# Decimal, complex inverse and finite-sum diagnosis

## Task context

- Task: explain the three Obj examples selected by the user and assess finite-sum evaluation.
- Scope: Number equality/inequality, complex division WD and proof search, sum expansion and `eval`.
- Related workspace: golitex, `examples/test_objs`.
- Date: 2026-10-02. The observations below were executed after a successful current-source release build. [Structured diagnostic probes](proof_journals/diagnosis_2026-10-02.json) record source/executable hashes, complete envelopes and exit codes, with both source and binary stable during the gate. Kernel changes were not made by this diagnosis.

## Decimal spelling is not normalized at construction

Observed in independent clean environments:

```litex
2.400 = 2.4          # rejected: search_proof, exit 1
2.400 + 0 = 2.4      # accepted: Calculation, exit 0
2.400 - 2.4 = 0      # accepted: Calculation, exit 0
2.400 != 2.4         # wrongly accepted: Closed decimal inequality, exit 0
```

The parser's `parse_number` concatenates the tokens but stores `"2.400"` without calling `normalize_decimal_number_string`. The number leaf of `evaluate_obj_to_normalized_decimal_number` returns a clone. Equality compares `left.normalized_value == right.normalized_value`; inequality compares `!=`. The ordinary algebraic scalar path also retains the literal spelling. Arithmetic operations such as addition/subtraction do call normalization, explaining the differing observations above. This is exact-string inconsistency, not floating-point rounding.

Source owners:

- [Parser construction](../../src/parse/object/primary.rs).
- [Number constructor](../../src/rational_expression/helper.rs).
- [Numeric leaf and existing decimal normalizer](../../src/rational_expression/decimal_arithmetic.rs).
- [Equality calculation](../../src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/verify_equality_by_builtin_rules/search_equal_fact_by_calculation.rs).
- [Inequality calculation](../../src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/search_atomic_except_equality_fact_proof_by_builtin_rules/not_equal.rs).

The false inequality is now an executable must-reject regression, [negative/number__n03.lit](negative/number__n03.lit), with its observed wrong acceptance recorded in `coverage.json`. The repair should establish canonical exact decimals at the existing construction boundary and audit both equality and inequality consumers; no new AST field is required by this diagnosis. The unchanged equality must accept and the unchanged inequality must reject after a repair. Also check integer-like decimals and zero spellings; do not normalize with floating point.

## Complex inverse has two successive missing proof routes

The user's follow-up spelled `1 / i = -1`. That statement is false: the correct inverse is `-i`.

```litex
i $in C           # accepted
i * i = -1        # accepted
i != 0            # rejected: search_proof
1 / i = -i        # rejected: well_defined
1 / i = -1        # rejected: well_defined, independently of its false RHS
```

`verify_div_obj_well_definedness_by_def` requires the divisor to be nonzero and both operands to belong to `C`. The direct `i != 0` requirement has no automatic proof in these probes. A contradiction proof was tested to isolate the next stage:

```litex
by contra:
    ? i != 0
    i * i = -1
    impossible i * i != 0

1 / i = -i
```

In successful runs of the contradiction step, it stores `i != 0`; the last equality then fails at `search_proof`, rather than `well_defined`. The incorrect `1 / i = -1` was also tested and rejected.

The contradiction proof itself is **not repeatable**, so it must not be promoted as a stable workaround. With the same source and executable hashes, 12 standalone runs accepted the nonzero proof 4 times and rejected it 8 times at `by_contra`. In 12 runs of the exact combined snippet above, the nonzero proof succeeded 7 times, followed by `search_proof` failure of the inverse; the other 5 runs failed the proof and then failed the inverse at `well_defined`. The structured journal retains every run. The cause of this variation has not been established by this diagnosis.

There is a second source barrier: `Calculation::Complex` allows nonzero denominators only when the real decimal evaluator can evaluate them to a nonzero number. It cannot evaluate `i`. The guarded rational strategy uses ordinary algebraic normalization, which does not apply `i² = -1`. Thus merely adding an automatic `i != 0` rule will not make this direct inverse succeed. A checked complex normalization route must consume the denominator's nonzero evidence as well.

Source owners:

- [Division WD](../../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs).
- [Complex calculation guard](../../src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/verify_equality_by_builtin_rules/search_equal_fact_by_calculation.rs).
- [Guarded ordinary rational strategy](../../src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/search_equal_fact_by_rational_with_nonzero_premises.rs).

## Finite sum needs substitution and folding

Observed:

```litex
sum(1, 3, fn(x Z) Z {x}) = 6  # rejected: search_proof
eval sum(1, 3, fn(x Z) Z {x})  # rejected: eval / unsupported_expression
eval fn(x Z) Z {x}(3)         # rejected: eval / unsupported_expression
```

Existing proof rules can verify these two source-ordered statements:

```litex
sum(1, 1, fn(x Z) Z {x}) = 1
sum(1, 2, fn(x Z) Z {x}) = sum(1, 1, fn(x Z) Z {x}) + 2
```

But appending `sum(1, 2, fn(x Z) Z {x}) = 3` still fails at `search_proof` in the tested environment. Adding the explicit arithmetic bridge `sum(1, 1, fn(x Z) Z {x}) + 2 = 3` also fails. These observations establish that partial expansion is present without a complete automatic fold/rewrite route; they do not establish that every explicit proof formulation is impossible.

The `evaluate_obj` dispatcher accepts closed numeric trees, arithmetic operators and stored-algorithm calls with a plain identifier head. It has no `IteratedOperator::Sum` branch and no general anonymous-function evaluation branch. `eval` currently returns display evaluation evidence and stores no mathematical equality fact.

Proposed computational reduction, not currently implemented or verified:

```text
sum(1, 3, f)
  -> f(1) + f(2) + f(3)
  -> 1 + 2 + 3
  -> 6
```

The proposed shared mechanism should first check WD/domain obligations, enumerate concrete integer endpoints, substitute each index into the function body without capturing binders, then evaluate and add terms exactly. A proof-producing consumer should retain evidence for the original-to-result equality; `eval` can display the result while the equality verifier checks that evidence. Extending display-only `eval` by itself does not make `sum(...) = 6` verify. Expansion needs a term/work budget; symbolic endpoints need a separate theorem/induction route. Keep the current nonempty-range contract unchanged until the user chooses otherwise.

Source owners:

- [Eval dispatcher](../../src/execute/execute_eval_stmt/evaluate_obj.rs).
- [Eval statement pipeline](../../src/execute/execute_eval_stmt/exec_eval_stmt.rs).
- [Sum WD](../../src/execute/execute_fact_stmt/well_defined_results/verify_obj/iterated.rs).
- [Single-term rule](../../src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/verify_equality_by_builtin_rules/by_equality_identities_wave11.rs).
- [Split-last rule](../../src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/verify_equality_by_builtin_rules/by_equality_identities_wave12.rs).

## Focused acceptance commands

```sh
python3 examples/test_objs/run.py --object number --baseline --report examples/test_objs/number_diagnosis_baseline.json
python3 examples/test_objs/run.py --object number --report examples/test_objs/number_diagnosis_results.json
```

The first must reproduce the Number observations. The second must currently fail on P03 and N03, keeping both defects visible. These are focused snapshots; the original complete-suite reports remain historical snapshots of the earlier inventory.

Checked follow-up: inventory audit passed; Number baseline reproduced both defects; the Number intended gate returned exit 1 with exactly the P03 rejection and N03 incorrect admission. No full-suite rerun is claimed.
