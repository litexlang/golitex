# src basic audit: tests/unit/execute/wd_obligations/tests.rs

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

## finite_set_fold_preserves_valid_domain_literals_and_named_iterands

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn finite_set_fold_preserves_valid_domain_literals_and_named_iterands() {
    let mut rt = runtime();
    let mut result = rt.run_litex_code(include_str!(
        "../../../../examples/wd/finite_set_fold_domain.lit"
    )).unwrap();
    result.attach_normal_json(&rt, "eval", None);
    assert!(result.success, "{}", result.normal_json.as_deref().unwrap());
    assert!(result.session_error.is_none());
}
```

Observed failure excerpt:

```text
thread 'execute::wd_obligation_tests::finite_set_fold_preserves_valid_domain_literals_and_named_iterands' (71852967) panicked at src/execute/../../tests/unit/execute/wd_obligations/tests.rs:81:5:
{
  "kind": "run",
  "success": false,
  "target": "eval",
  "path": null,
  "detail": "normal",
  "language": "en",
  "statement_results": [
    {
      "success": false,
      "statement": "let …",
      "why_failed": {
        "type": "define_obj",
        "rule_name": "Let binding",
        "message": "Bind a name to a well-defined value",
        "phase": "let",
        "failure": {
          "success": false,
          "obj": "finite_set_reduce({1, 2}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 0)",
          "phase": "well_defined",
          "failure": {
            "phase": "IteratedOperator",
            "failure": {
              "phase": "FiniteSetReduce",
              "failure": {
                "phase": "requirement",
                "obj": "finite_set_reduce({1, 2}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 0)",
                "result": {
                  "type": "forall",
                  "success": false,
                  "phase": "search_proof",
                  "fact": "forall __param_5, __param_6, __param_7 Z:\n    fn (a, b Z) Z{a + b}(__param_5, __param_6) = __param_5 + __param_6\n    fn (a, b Z) Z{a + b}(__param_6, __param_7) = __param_6 + __param_7\n    fn (a, b Z) Z{a + b}(fn (a, b Z) Z{a + b}(__param_5, __param_6), __param_7) = fn (a, b Z) Z{a + b}(__param_5 + __param_6, __param_7)\n    fn (a, b Z) Z{a + b}(__param_5 + __param_6, __param_7) = __param_5 + __param_6 + __param_7\n    fn (a, b Z) Z{a + b}(__param_5, fn (a, b Z) Z{a + b}(__param_6, __param_7)) = fn (a, b Z) Z{a + b}(__param_5, __param_6 + __param_7)\n    fn (a, b Z) Z{a + b}(__param_5, __param_
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::wd_obligation_tests::finite_set_fold_preserves_valid_domain_literals_and_named_iterands -- --exact --nocapture
```

