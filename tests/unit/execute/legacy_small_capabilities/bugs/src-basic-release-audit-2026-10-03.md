# src basic audit: tests/unit/execute/legacy_small_capabilities/tests.rs

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

## legacy_small_ordered_reduce

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn legacy_small_ordered_reduce() {
    let evidence = check("reduce(1,3,fn(k Z) Z {k},fn(a,b Z) Z {a+b},0) = 6", true);
    for key in [
        "AggregateCalculation",
        "\"reduce\"",
        "\"term\"",
        "\"operation\"",
        "\"accumulated_value\"",
    ] {
        assert!(evidence.contains(key), "missing {key}");
    }
    check("reduce(1,3,fn(k Z) Z {k},fn(a,b Z) Z {a-b},0) = -6", true);
    check("reduce(1,3,fn(k Z) Z {k},fn(a,b Z) Z {a-b},0) = 2", false);
    check("reduce(1,3,fn(k Z) Z {k},fn(a,b Z) Z {a+b},0) = 7", false);
    check(
        "reduce(1,3,fn(k Z) R {k},fn(a,b R) R {a*b},1) = product(1,3,fn(k Z) R {k})",
        true,
    );
    check(
        "reduce(1,3,fn(k Z) R {k},fn(a,b R) R {a*b},2) = product(1,3,fn(k Z) R {k})",
        false,
    );
    check("reduce(3,1,fn(k Z) Z {k},fn(a,b Z) Z {a+b},5) = 5", true);
    check(
        "reduce(1,1025,fn(k Z) Z {k},fn(a,b Z) Z {a+b},0) = 525825",
        false,
    );
}
```

Observed failure excerpt:

```text
thread '<unnamed>' (71852826) panicked at src/execute/../../tests/unit/execute/legacy_small_capabilities/tests.rs:18:13:
assertion `left == right` failed: reduce(1,3,fn(k Z) Z {k},fn(a,b Z) Z {a+b},0) = 6
{
  "kind": "run",
  "success": false,
  "target": "eval",
  "path": null,
  "detail": "detailed",
  "language": "en",
  "statement_results": [
    {
      "success": false,
      "kind": "fact",
      "statement": "reduce(1, 3, fn (k Z) Z{k}, fn (a, b Z) Z{a + b}, 0) = 6",
      "verify": {
        "type": "equality",
        "success": false,
        "phase": "search_proof",
        "fact": "reduce(1, 3, fn (k Z) Z{k}, fn (a, b Z) Z{a + b}, 0) = 6",
        "well_defined": {
          "left": {
            "type": "by_def",
            "family": "IteratedOperator",
            "kind": "Reduce",
            "obj": "reduce(1, 3, fn (k Z) Z{k}, fn (a, b Z) Z{a + b}, 0)",
            "child_obj_well_defined": [
              {
                "type": "by_def",
                "family": "Literal",
                "kind": "Number",
                "obj": "1"
              },
              {
                "type": "by_def",
                "family": "Literal",
                "kind": "Number",
                "obj": "3"
              },
              {
                "type": "by_def",
                "family": "FunctionSpace",
                "kind": "AnonymousFn",
                "obj": "fn (k Z) Z{k}",
                "param_type_well_defined": [
                  {
                    "type": "by_def",
                    "family": "StandardSet",
                    "kind": "StandardSet",
                    "obj": "Z"
                  }
                ],
                "dom_fact_well_defined": [],
                "ret_set_well_defined": {
                  "type":
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::legacy_small_capability_repair_tests::legacy_small_ordered_reduce -- --exact --nocapture
```

## legacy_small_unordered_fold_laws

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn legacy_small_unordered_fold_laws() {
    check(
        "finite_set_reduce({1,2},fn(k R) R {k},fn(a,b R) R {a+b},0) $in R",
        true,
    );
    check(
        "finite_set_reduce({1,2},fn(k R) R {k},fn(a,b R) R {a-b},0) $in R",
        false,
    );
    // Commutativity alone is insufficient: this symmetric operation is not
    // associative, and enumeration order would change the resulting value.
    check(
        "finite_set_reduce({1,2},fn(k R) R {k},fn(a,b R) R {(a+b)/2},0) $in R",
        false,
    );
    check("forall a Z,n N:\n    a^n $in Z", true);
    check("2^(-1) $in Z", false);
    check("forall a Z,m N+:\n    (a%m) $in Z", true);
    check(
        "forall A finite_set,B set,f fn(x A)B:\n    $is_finite_set(fn_range(f))",
        true,
    );
    check("forall f fn(x R)R:\n    $is_finite_set(fn_range(f))", false);
    let evidence = check(
        "finite_set_reduce({3,1,2},fn(k R) R {k},fn(a,b R) R {a+b},0) = 6",
        true,
    );
    assert!(evidence.contains("finite_set_reduce") && evidence.contains("operation"));
    check(
        "finite_set_reduce({1,1},fn(k R) R {k},fn(a,b R) R {a+b},0) = 1",
        false,
    );
    check(
        "finite_set_reduce({1,2,3},fn(k R) R {k},fn(a,b R) R {a+b},0) = 7",
        false,
    );
}
```

Observed failure excerpt:

```text
thread '<unnamed>' (71852848) panicked at src/execute/../../tests/unit/execute/legacy_small_capabilities/tests.rs:18:13:
assertion `left == right` failed: finite_set_reduce({1,2},fn(k R) R {k},fn(a,b R) R {a+b},0) $in R
{
  "kind": "run",
  "success": false,
  "target": "eval",
  "path": null,
  "detail": "detailed",
  "language": "en",
  "statement_results": [
    {
      "success": false,
      "kind": "fact",
      "statement": "<wd_failed>",
      "verify": {
        "type": "atomic_except_equality",
        "success": false,
        "phase": "well_defined",
        "failure": {
          "phase": "IteratedOperator",
          "failure": {
            "phase": "FiniteSetReduce",
            "failure": {
              "phase": "requirement",
              "obj": "finite_set_reduce({1, 2}, fn (k R) R{k}, fn (a, b R) R{a + b}, 0)",
              "result": {
                "type": "forall",
                "success": false,
                "phase": "search_proof",
                "fact": "forall __param_4, __param_5, __param_6 R:\n    fn (a, b R) R{a + b}(__param_4, __param_5) = __param_4 + __param_5\n    fn (a, b R) R{a + b}(__param_5, __param_6) = __param_5 + __param_6\n    fn (a, b R) R{a + b}(fn (a, b R) R{a + b}(__param_4, __param_5), __param_6) = fn (a, b R) R{a + b}(__param_4 + __param_5, __param_6)\n    fn (a, b R) R{a + b}(__param_4 + __param_5, __param_6) = __param_4 + __param_5 + __param_6\n    fn (a, b R) R{a + b}(__param_4, fn (a, b R) R{a + b}(__param_5, __param_6)) = fn (a, b R) R{a + b}(__param_4, __param_5 + __param_6)\n    fn (a, b R) R{a + b}(__param_4, __param_5 + __param_6) = __param_4 + (__param_5 + __param_6)\n    __param_4 + __param_5 + __param_6 = __param_4 + (__param_5 + __param_6)\n    fn (a, b R) R{a + b}(fn (a, b R) R{a + b}(__param_4, __p
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::legacy_small_capability_repair_tests::legacy_small_unordered_fold_laws -- --exact --nocapture
```

