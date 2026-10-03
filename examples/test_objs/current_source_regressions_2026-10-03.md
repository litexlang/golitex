# Current-source Obj regressions observed on 2026-10-03

Task: preserve exact full-corpus failures discovered during the numeric powers, fraction order, periodic trig and numeric modulus implementation.

This stable current-source gate used source `9a8e89bf05c2130634abfe5e8e82b7758e47c158160813561a7d40d316c21c34` and binary `a3bcaa8de4825bfb6780178e9cb2a8e2e0a711ddc575617d3c4e75266d3df7ea`. It found 37 rejected owning positive files and two process/protocol failures; all 289 negative fixtures still rejected. Earlier retained releases passed these owning files. The exact mathematical cause of each new failure is not yet established.

Full original files, exact diagnostics and commands are retained in [the source/output journal](proof_journals/current_source_regressions_2026-10-03.json). This page does not treat the failures as successful regressions. The existing direct-gap list remains separate.

## fn_obj

- Reproduction: [fn_obj.lit](fn_obj.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/fn_obj.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
f(2)(3) = fn (y R) R{2 + y}(3) = 2 + 3 = 5
```

## div

- Reproduction: [div.lit](div.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/div.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
1 / (2 * i) = -i / 2
```

## exp

- Reproduction: [exp.lit](exp.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/exp.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
exp(ln(2)) = 2
```

## sqrt

- Reproduction: [sqrt.lit](sqrt.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/sqrt.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
sqrt (2) ^ 2 = 2
```

## real_part

- Reproduction: [real_part.lit](real_part.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/real_part.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
re(-2 - i) = re(-2) - re(i) = -2 - 0 = -2
```

## imaginary_part

- Reproduction: [imaginary_part.lit](imaginary_part.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/imaginary_part.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
img(-2 - i) = img(-2) - img(i) = 0 - 1 = -1
```

## union

- Reproduction: [union.lit](union.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/union.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
by extension
```

## intersect

- Reproduction: [intersect.lit](intersect.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/intersect.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
by extension
```

## set_minus

- Reproduction: [set_minus.lit](set_minus.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/set_minus.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
by extension
```

## index_union

- Reproduction: [index_union.lit](index_union.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/index_union.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
let …
```

## index_intersect

- Reproduction: [index_intersect.lit](index_intersect.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/index_intersect.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
let …
```

## index_cart

- Reproduction: [index_cart.lit](index_cart.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/index_cart.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
let …
```

## list_set

- Reproduction: [list_set.lit](list_set.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/list_set.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
not 3 $in {1, 2}
```

## set_builder

- Reproduction: [set_builder.lit](set_builder.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/set_builder.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
let …
```

## range

- Reproduction: [range.lit](range.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/range.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
range(2, 2) = {}
```

## closed_range

- Reproduction: [closed_range.lit](closed_range.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/closed_range.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
closed_range(3, 1) = {}
```

## cart

- Reproduction: [cart.lit](cart.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/cart.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
((1, 2), 3) $in cart(cart(R, Z), N)
```

## fn_set

- Reproduction: [fn_set.lit](fn_set.lit).
- Observation: `reject`, phase `parse`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/fn_set.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
Runtime(ParseError(RuntimeParseError { message: "undefined name `x`", line: 22, path: Real("examples/test_objs/fn_set.lit") }))
```

## anonymous_fn

- Reproduction: [anonymous_fn.lit](anonymous_fn.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/anonymous_fn.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
fn (x R) R{x + y}(2) = 2 + y = 2 + 3 = 5
```

## fn_range

- Reproduction: [fn_range.lit](fn_range.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/fn_range.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
by extension
```

## sum

- Reproduction: [sum.lit](sum.lit).
- Observation: `infrastructure_failure`, phase `protocol`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/sum.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
No diagnostic was emitted; process/protocol failure. The journal retains the complete source reproduction.
```

## product

- Reproduction: [product.lit](product.lit).
- Observation: `infrastructure_failure`, phase `protocol`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/product.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
No diagnostic was emitted; process/protocol failure. The journal retains the complete source reproduction.
```

## sum_of_finite_set

- Reproduction: [sum_of_finite_set.lit](sum_of_finite_set.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/sum_of_finite_set.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
finite_set_sum(S, fn (k S) R{c}) = finite_set_size(S) * c
```

## product_of_finite_set

- Reproduction: [product_of_finite_set.lit](product_of_finite_set.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/product_of_finite_set.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
{"success": false, "statement": "sketch", "why_failed": {"type": "proof_block", "rule_name": "Sketch", "message": "Run a sketch proof block", "phase": "sketch", "failure": {"step_index": 3, "result": {"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "IteratedOperator", "failure": {"phase": "ProductOfFiniteSet", "failure": {"phase": "requirement", "obj": "finite_set_product({1 / 2, 1 / 3}, fn (k Q) Q{k})", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{1 / 2, 1 / 3} $subset Q", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{1 / 2, 1 / 3}", "child_obj_well_defined": [{"type": "by_def", "family": "ArithmeticOperator", "kind": "Div", "obj": "1 / 2", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}, {"type": "by_def", "family": "Literal", "kind": "Number", "obj": "2"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "2 != 0", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "2"}, {"type": "by_def", "family": "Literal", "kind": "Number", "obj": "0"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "NotEqualFact", "rule": "ClosedDecimal", "left_normal": "2", "right_normal": "0"}}, {"type": "atomic_except_equality", "success": true, "fact": "1 $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "ClosedNumericMembership"}}, {"type": "atomic_except_equality", "success": true, "fact": "2 $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "2"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "ClosedNumericMembership"}}]}, {"type": "by_def", "family": "ArithmeticOperator", "kind": "Div", "obj": "1 / 3", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}, {"type": "by_def", "family": "Literal", "kind": "Number", "obj": "3"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "3 != 0", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "3"}, {"type": "by_def", "family": "Literal", "kind": "Number", "obj": "0"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "NotEqualFact", "rule": "ClosedDecimal", "left_normal": "3", "right_normal": "0"}}, {"type": "atomic_except_equality", "success": true, "fact": "1 $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "ClosedNumericMembership"}}, {"type": "atomic_except_equality", "success": true, "fact": "3 $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "3"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "ClosedNumericMembership"}}]}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "1 / 2 != 1 / 3", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "ArithmeticOperator", "kind": "Div", "obj": "1 / 2", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}, {"type": "by_def", "family": "Literal", "kind": "Number", "obj": "2"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "2 != 0", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "2"}, {"type": "by_def", "family": "Literal", "kind": "Number", "obj": "0"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "NotEqualFact", "rule": "ClosedDecimal", "left_normal": "2", "right_normal": "0"}}, {"type": "atomic_except_equality", "success": true, "fact": "1 $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "ClosedNumericMembership"}}, {"type": "atomic_except_equality", "success": true, "fact": "2 $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "2"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "ClosedNumericMembership"}}]}, {"type": "by_def", "family": "ArithmeticOperator", "kind": "Div", "obj": "1 / 3", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}, {"type": "by_def", "family": "Literal", "kind": "Number", "obj": "3"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "3 != 0", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "3"}, {"type": "by_def", "family": "Literal", "kind": "Number", "obj": "0"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "NotEqualFact", "rule": "ClosedDecimal", "left_normal": "3", "right_normal": "0"}}, {"type": "atomic_except_equality", "success": true, "fact": "1 $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "ClosedNumericMembership"}}, {"type": "atomic_except_equality", "success": true, "fact": "3 $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "3"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "ClosedNumericMembership"}}]}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "rule": "ClosedRational", "left_normal": "1 / 2", "right_normal": "1 / 3"}}]}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "Q"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}}}}}}}, "stores": [], "infers": []}}}, "stores": [], "infers": []}
```

## reduce

- Reproduction: [reduce.lit](reduce.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/reduce.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
reduce(2, 2, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 0) = 2
```

## finite_set_reduce

- Reproduction: [finite_set_reduce.lit](finite_set_reduce.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/finite_set_reduce.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
{"success": false, "statement": "sketch", "why_failed": {"type": "proof_block", "rule_name": "Sketch", "message": "Run a sketch proof block", "phase": "sketch", "failure": {"step_index": 0, "result": {"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "IteratedOperator", "failure": {"phase": "FiniteSetReduce", "failure": {"phase": "requirement", "obj": "finite_set_reduce({}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 7)", "result": {"type": "forall", "success": false, "phase": "search_proof", "fact": "forall __param_4, __param_5, __param_6 Z:\n    fn (a, b Z) Z{a + b}(__param_4, __param_5) = __param_4 + __param_5\n    fn (a, b Z) Z{a + b}(__param_5, __param_6) = __param_5 + __param_6\n    fn (a, b Z) Z{a + b}(fn (a, b Z) Z{a + b}(__param_4, __param_5), __param_6) = fn (a, b Z) Z{a + b}(__param_4 + __param_5, __param_6)\n    fn (a, b Z) Z{a + b}(__param_4 + __param_5, __param_6) = __param_4 + __param_5 + __param_6\n    fn (a, b Z) Z{a + b}(__param_4, fn (a, b Z) Z{a + b}(__param_5, __param_6)) = fn (a, b Z) Z{a + b}(__param_4, __param_5 + __param_6)\n    fn (a, b Z) Z{a + b}(__param_4, __param_5 + __param_6) = __param_4 + (__param_5 + __param_6)\n    __param_4 + __param_5 + __param_6 = __param_4 + (__param_5 + __param_6)\n    fn (a, b Z) Z{a + b}(fn (a, b Z) Z{a + b}(__param_4, __param_5), __param_6) = fn (a, b Z) Z{a + b}(__param_4, fn (a, b Z) Z{a + b}(__param_5, __param_6))", "introduced_params": {"param_type_well_defined": [{"type": "obj", "well_defined": {"success": true, "proof": {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "Z"}}}], "defined_params": {"stores": [{"fact_id": "f1201"}, {"fact_id": "f1202"}, {"fact_id": "f1203"}], "infers": []}}, "assumed_dom_facts": [], "proved_then_facts": [{"verify_result": {"type": "equality", "success": true, "fact": "fn (a, b Z) Z{a + b}(__param_4, __param_5) = __param_4 + __param_5", "well_defined": {"left": {"type": "by_def", "family": "FnObj", "kind": "FnObj", "obj": "fn (a, b Z) Z{a + b}(__param_4, __param_5)", "child_obj_well_defined": [{"type": "by_def", "family": "FunctionSpace", "kind": "AnonymousFn", "obj": "fn (a, b Z) Z{a + b}", "param_type_well_defined": [{"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "dom_fact_well_defined": [], "ret_set_well_defined": {"type": "by_known", "obj": "Z", "wd_id": "wd26"}, "body_well_defined": {"type": "by_def", "family": "ArithmeticOperator", "kind": "Add", "obj": "a + b", "child_obj_well_defined": [{"type": "by_known", "obj": "a", "wd_id": "wd29"}, {"type": "by_known", "obj": "b", "wd_id": "wd30"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "a $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "a", "wd_id": "wd29"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "a $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "a", "wd_id": "wd29"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1204", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}, {"type": "atomic_except_equality", "success": true, "fact": "b $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "b", "wd_id": "wd30"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "b $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "b", "wd_id": "wd30"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1205", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}]}, "body_in_ret_set": {"type": "atomic_except_equality", "success": true, "fact": "a + b $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "ArithmeticOperator", "kind": "Add", "obj": "a + b", "child_obj_well_defined": [{"type": "by_known", "obj": "a", "wd_id": "wd29"}, {"type": "by_known", "obj": "b", "wd_id": "wd30"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "a $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "a", "wd_id": "wd29"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "a $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "a", "wd_id": "wd29"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1204", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}, {"type": "atomic_except_equality", "success": true, "fact": "b $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "b", "wd_id": "wd30"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "b $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "b", "wd_id": "wd30"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1205", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}]}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "IntegerArithmeticClosure", "operand_proofs": [{"type": "atomic_except_equality", "success": true, "fact": "a $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "a", "wd_id": "wd29"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1204", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}, {"type": "atomic_except_equality", "success": true, "fact": "b $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "b", "wd_id": "wd30"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1205", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}]}}}, {"type": "by_known", "obj": "__param_4", "wd_id": "wd25"}, {"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "__param_4 $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_4", "wd_id": "wd25"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1201", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}, {"type": "atomic_except_equality", "success": true, "fact": "__param_5 $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1202", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}], "domain_fn_set": {"type": "anonymous_literal", "fn_set": "fn (a, b Z) Z"}}, "right": {"type": "by_def", "family": "ArithmeticOperator", "kind": "Add", "obj": "__param_4 + __param_5", "child_obj_well_defined": [{"type": "by_known", "obj": "__param_4", "wd_id": "wd25"}, {"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "__param_4 $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_4", "wd_id": "wd25"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "__param_4 $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_4", "wd_id": "wd25"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1201", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}, {"type": "atomic_except_equality", "success": true, "fact": "__param_5 $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "__param_5 $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1202", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}]}}, "searched_proof": {"type": "by_object_definition", "kind": "fn_application_have_fn_equal", "function_equal": [], "expanded_body": "__param_4 + __param_5", "residual_equal": {"type": "equality", "success": true, "fact": "__param_4 + __param_5 = __param_4 + __param_5", "well_defined": {"left": {"type": "by_def", "family": "ArithmeticOperator", "kind": "Add", "obj": "__param_4 + __param_5", "child_obj_well_defined": [{"type": "by_known", "obj": "__param_4", "wd_id": "wd25"}, {"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "__param_4 $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_4", "wd_id": "wd25"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "__param_4 $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_4", "wd_id": "wd25"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1201", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}, {"type": "atomic_except_equality", "success": true, "fact": "__param_5 $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "__param_5 $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1202", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}]}, "right": {"type": "by_def", "family": "ArithmeticOperator", "kind": "Add", "obj": "__param_4 + __param_5", "child_obj_well_defined": [{"type": "by_known", "obj": "__param_4", "wd_id": "wd25"}, {"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "__param_4 $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_4", "wd_id": "wd25"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "__param_4 $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_4", "wd_id": "wd25"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1201", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}, {"type": "atomic_except_equality", "success": true, "fact": "__param_5 $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "__param_5 $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1202", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}]}}, "searched_proof": {"type": "by_they_are_the_same", "kind": "same_ir"}}}}, "store_and_infer": {"stores": [{"fact_id": "f1192"}], "infers": []}}, {"verify_result": {"type": "equality", "success": true, "fact": "fn (a, b Z) Z{a + b}(__param_5, __param_6) = __param_5 + __param_6", "well_defined": {"left": {"type": "by_def", "family": "FnObj", "kind": "FnObj", "obj": "fn (a, b Z) Z{a + b}(__param_5, __param_6)", "child_obj_well_defined": [{"type": "by_def", "family": "FunctionSpace", "kind": "AnonymousFn", "obj": "fn (a, b Z) Z{a + b}", "param_type_well_defined": [{"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "dom_fact_well_defined": [], "ret_set_well_defined": {"type": "by_known", "obj": "Z", "wd_id": "wd26"}, "body_well_defined": {"type": "by_def", "family": "ArithmeticOperator", "kind": "Add", "obj": "a + b", "child_obj_well_defined": [{"type": "by_known", "obj": "a", "wd_id": "wd37"}, {"type": "by_known", "obj": "b", "wd_id": "wd38"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "a $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "a", "wd_id": "wd37"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "a $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "a", "wd_id": "wd37"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1820", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}, {"type": "atomic_except_equality", "success": true, "fact": "b $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "b", "wd_id": "wd38"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "b $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "b", "wd_id": "wd38"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1821", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}]}, "body_in_ret_set": {"type": "atomic_except_equality", "success": true, "fact": "a + b $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "ArithmeticOperator", "kind": "Add", "obj": "a + b", "child_obj_well_defined": [{"type": "by_known", "obj": "a", "wd_id": "wd37"}, {"type": "by_known", "obj": "b", "wd_id": "wd38"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "a $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "a", "wd_id": "wd37"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "a $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "a", "wd_id": "wd37"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1820", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}, {"type": "atomic_except_equality", "success": true, "fact": "b $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "b", "wd_id": "wd38"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "b $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "b", "wd_id": "wd38"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1821", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}]}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "IntegerArithmeticClosure", "operand_proofs": [{"type": "atomic_except_equality", "success": true, "fact": "a $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "a", "wd_id": "wd37"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1820", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}, {"type": "atomic_except_equality", "success": true, "fact": "b $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "b", "wd_id": "wd38"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1821", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}]}}}, {"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}, {"type": "by_known", "obj": "__param_6", "wd_id": "wd28"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "__param_5 $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1202", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}, {"type": "atomic_except_equality", "success": true, "fact": "__param_6 $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_6", "wd_id": "wd28"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1203", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}], "domain_fn_set": {"type": "anonymous_literal", "fn_set": "fn (a, b Z) Z"}}, "right": {"type": "by_def", "family": "ArithmeticOperator", "kind": "Add", "obj": "__param_5 + __param_6", "child_obj_well_defined": [{"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}, {"type": "by_known", "obj": "__param_6", "wd_id": "wd28"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "__param_5 $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "__param_5 $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1202", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}, {"type": "atomic_except_equality", "success": true, "fact": "__param_6 $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_6", "wd_id": "wd28"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "__param_6 $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_6", "wd_id": "wd28"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1203", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}]}}, "searched_proof": {"type": "by_object_definition", "kind": "fn_application_have_fn_equal", "function_equal": [], "expanded_body": "__param_5 + __param_6", "residual_equal": {"type": "equality", "success": true, "fact": "__param_5 + __param_6 = __param_5 + __param_6", "well_defined": {"left": {"type": "by_def", "family": "ArithmeticOperator", "kind": "Add", "obj": "__param_5 + __param_6", "child_obj_well_defined": [{"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}, {"type": "by_known", "obj": "__param_6", "wd_id": "wd28"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "__param_5 $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "__param_5 $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1202", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}, {"type": "atomic_except_equality", "success": true, "fact": "__param_6 $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_6", "wd_id": "wd28"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "__param_6 $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_6", "wd_id": "wd28"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1203", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}]}, "right": {"type": "by_def", "family": "ArithmeticOperator", "kind": "Add", "obj": "__param_5 + __param_6", "child_obj_well_defined": [{"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}, {"type": "by_known", "obj": "__param_6", "wd_id": "wd28"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "__param_5 $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "__param_5 $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1202", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}, {"type": "atomic_except_equality", "success": true, "fact": "__param_6 $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_6", "wd_id": "wd28"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "__param_6 $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_6", "wd_id": "wd28"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1203", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}]}}, "searched_proof": {"type": "by_they_are_the_same", "kind": "same_ir"}}}}, "store_and_infer": {"stores": [{"fact_id": "f1193"}], "infers": []}}], "failed_then_index": 2, "failed_then": {"type": "equality", "success": false, "phase": "search_proof", "fact": "fn (a, b Z) Z{a + b}(fn (a, b Z) Z{a + b}(__param_4, __param_5), __param_6) = fn (a, b Z) Z{a + b}(__param_4 + __param_5, __param_6)", "well_defined": {"left": {"type": "by_def", "family": "FnObj", "kind": "FnObj", "obj": "fn (a, b Z) Z{a + b}(fn (a, b Z) Z{a + b}(__param_4, __param_5), __param_6)", "child_obj_well_defined": [{"type": "by_def", "family": "FunctionSpace", "kind": "AnonymousFn", "obj": "fn (a, b Z) Z{a + b}", "param_type_well_defined": [{"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "dom_fact_well_defined": [], "ret_set_well_defined": {"type": "by_known", "obj": "Z", "wd_id": "wd26"}, "body_well_defined": {"type": "by_def", "family": "ArithmeticOperator", "kind": "Add", "obj": "a + b", "child_obj_well_defined": [{"type": "by_known", "obj": "a", "wd_id": "wd45"}, {"type": "by_known", "obj": "b", "wd_id": "wd46"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "a $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "a", "wd_id": "wd45"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "a $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "a", "wd_id": "wd45"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f2444", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}, {"type": "atomic_except_equality", "success": true, "fact": "b $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "b", "wd_id": "wd46"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "b $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "b", "wd_id": "wd46"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f2445", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}]}, "body_in_ret_set": {"type": "atomic_except_equality", "success": true, "fact": "a + b $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "ArithmeticOperator", "kind": "Add", "obj": "a + b", "child_obj_well_defined": [{"type": "by_known", "obj": "a", "wd_id": "wd45"}, {"type": "by_known", "obj": "b", "wd_id": "wd46"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "a $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "a", "wd_id": "wd45"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "a $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "a", "wd_id": "wd45"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f2444", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}, {"type": "atomic_except_equality", "success": true, "fact": "b $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "b", "wd_id": "wd46"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "b $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "b", "wd_id": "wd46"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f2445", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}]}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "IntegerArithmeticClosure", "operand_proofs": [{"type": "atomic_except_equality", "success": true, "fact": "a $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "a", "wd_id": "wd45"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f2444", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}, {"type": "atomic_except_equality", "success": true, "fact": "b $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "b", "wd_id": "wd46"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f2445", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}]}}}, {"type": "by_known", "obj": "fn (a, b Z) Z{a + b}(__param_4, __param_5)", "wd_id": "wd35"}, {"type": "by_known", "obj": "__param_6", "wd_id": "wd28"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "fn (a, b Z) Z{a + b}(__param_4, __param_5) $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "fn (a, b Z) Z{a + b}(__param_4, __param_5)", "wd_id": "wd35"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_special_property", "rule": "AnonymousFnApplicationInCodomain", "signature": "fn (a, b Z) Z", "applied_return_set": "Z", "return_set_match": {"type": "by_they_are_the_same", "kind": "same_ir"}}}, {"type": "atomic_except_equality", "success": true, "fact": "__param_6 $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_6", "wd_id": "wd28"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1203", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}], "domain_fn_set": {"type": "anonymous_literal", "fn_set": "fn (a, b Z) Z"}}, "right": {"type": "by_def", "family": "FnObj", "kind": "FnObj", "obj": "fn (a, b Z) Z{a + b}(__param_4 + __param_5, __param_6)", "child_obj_well_defined": [{"type": "by_def", "family": "FunctionSpace", "kind": "AnonymousFn", "obj": "fn (a, b Z) Z{a + b}", "param_type_well_defined": [{"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "dom_fact_well_defined": [], "ret_set_well_defined": {"type": "by_known", "obj": "Z", "wd_id": "wd26"}, "body_well_defined": {"type": "by_def", "family": "ArithmeticOperator", "kind": "Add", "obj": "a + b", "child_obj_well_defined": [{"type": "by_known", "obj": "a", "wd_id": "wd47"}, {"type": "by_known", "obj": "b", "wd_id": "wd48"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "a $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "a", "wd_id": "wd47"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "a $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "a", "wd_id": "wd47"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f2727", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}, {"type": "atomic_except_equality", "success": true, "fact": "b $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "b", "wd_id": "wd48"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "b $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "b", "wd_id": "wd48"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f2728", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}]}, "body_in_ret_set": {"type": "atomic_except_equality", "success": true, "fact": "a + b $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "ArithmeticOperator", "kind": "Add", "obj": "a + b", "child_obj_well_defined": [{"type": "by_known", "obj": "a", "wd_id": "wd47"}, {"type": "by_known", "obj": "b", "wd_id": "wd48"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "a $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "a", "wd_id": "wd47"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "a $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "a", "wd_id": "wd47"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f2727", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}, {"type": "atomic_except_equality", "success": true, "fact": "b $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "b", "wd_id": "wd48"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "StandardSetSubsetMembership", "source_set": "Z", "source_membership_proof": {"type": "atomic_except_equality", "success": true, "fact": "b $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "b", "wd_id": "wd48"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f2728", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}}}]}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "IntegerArithmeticClosure", "operand_proofs": [{"type": "atomic_except_equality", "success": true, "fact": "a $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "a", "wd_id": "wd47"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f2727", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}, {"type": "atomic_except_equality", "success": true, "fact": "b $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "b", "wd_id": "wd48"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f2728", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}]}}}, {"type": "by_known", "obj": "__param_4 + __param_5", "wd_id": "wd36"}, {"type": "by_known", "obj": "__param_6", "wd_id": "wd28"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "__param_4 + __param_5 $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_4 + __param_5", "wd_id": "wd36"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "builtin_rule", "family": "InFact", "rule": "IntegerArithmeticClosure", "operand_proofs": [{"type": "atomic_except_equality", "success": true, "fact": "__param_4 $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_4", "wd_id": "wd25"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1201", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}, {"type": "atomic_except_equality", "success": true, "fact": "__param_5 $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_5", "wd_id": "wd27"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1202", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}]}}, {"type": "atomic_except_equality", "success": true, "fact": "__param_6 $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_known", "obj": "__param_6", "wd_id": "wd28"}, {"type": "by_known", "obj": "Z", "wd_id": "wd26"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}, "searched_proof": {"type": "by_known_atomic", "cite_fact_id": "f1203", "why_parameters_of_known_fact_are_equal_to_givens": [{"type": "by_they_are_the_same", "kind": "same_ir"}, {"type": "by_they_are_the_same", "kind": "same_ir"}]}}], "domain_fn_set": {"type": "anonymous_literal", "fn_set": "fn (a, b Z) Z"}}}}}}}}}}, "stores": [], "infers": []}}}, "stores": [], "infers": []}
```

## struct_obj

- Reproduction: [struct_obj.lit](struct_obj.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/struct_obj.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
have … = …
```

## field_access

- Reproduction: [field_access.lit](field_access.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/field_access.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
have … = …
```

## instantiated_template_obj

- Reproduction: [instantiated_template_obj.lit](instantiated_template_obj.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/instantiated_template_obj.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
{"success": false, "statement": "sketch", "why_failed": {"type": "proof_block", "rule_name": "Sketch", "message": "Run a sketch proof block", "phase": "sketch", "failure": {"step_index": 2, "result": {"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "FnObj", "failure": {"message": "no matching function signature"}}}}, "stores": [], "infers": []}}}, "stores": [], "infers": []}
```

## standard_set_r_pos

- Reproduction: [standard_set_r_pos.lit](standard_set_r_pos.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/standard_set_r_pos.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
sqrt (2) > 0
```

## standard_set_r_star

- Reproduction: [standard_set_r_star.lit](standard_set_r_star.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/standard_set_r_star.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
sqrt (2) $in R*
```

## one_side_interval_lower_open

- Reproduction: [one_side_interval_lower_open.lit](one_side_interval_lower_open.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/one_side_interval_lower_open.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
1 $in '(0,)
```

## one_side_interval_lower_closed

- Reproduction: [one_side_interval_lower_closed.lit](one_side_interval_lower_closed.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/one_side_interval_lower_closed.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
0 $in '[0,)
```

## one_side_interval_upper_open

- Reproduction: [one_side_interval_upper_open.lit](one_side_interval_upper_open.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/one_side_interval_upper_open.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
-1 $in '(,0)
```

## one_side_interval_upper_closed

- Reproduction: [one_side_interval_upper_closed.lit](one_side_interval_upper_closed.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/one_side_interval_upper_closed.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
0 $in '(,0]
```

## interval_open_open

- Reproduction: [interval_open_open.lit](interval_open_open.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/interval_open_open.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
not -1 $in '(0, 2)
```

## interval_open_closed

- Reproduction: [interval_open_closed.lit](interval_open_closed.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/interval_open_closed.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
not -1 $in '(0, 2]
```

## interval_closed_open

- Reproduction: [interval_closed_open.lit](interval_closed_open.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/interval_closed_open.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
not -1 $in '[0, 2)
```

## interval_closed_closed

- Reproduction: [interval_closed_closed.lit](interval_closed_closed.lit).
- Observation: `reject`, phase `sketch`, exit `1`.
- Primary label: `kernel_problem`, provisional; the failing semantic owner is not localized.
- Execution category: diagnosing; a shared representation, lifecycle, storage or verifier-ceiling repair needs a separate architectural decision.
- Acceptance: `target/release/litex -strict -f examples/test_objs/interval_closed_closed.lit` must accept the unchanged valid file while the owning rejection fixtures continue rejecting.
- Next action: locate the earliest failing source step/WD/premise using the exact journal; do not assume that raising search permissions is the repair.

Captured failing statement or diagnostic:

```text
not -1 $in '[0, 2]
```

