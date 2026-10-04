# src basic audit: src/execute/execute_eval_stmt/exec_eval_stmt_tests.rs

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

## aggregate_algorithm_terms_keep_checked_equations_and_eval_stores_empty

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn aggregate_algorithm_terms_keep_checked_equations_and_eval_stores_empty() {
    let mut rt = runtime_with_file_env();
    assert!(!exec_one(
        &mut rt,
        "algo flag(x R) R by cases:\n    case x = 0: 0\n    case x != 0: 1"
    )
    .is_failed());
    let before = rt.top_exec_env().facts.facts_by_id.len();
    assert_eval_number(&mut rt, "eval sum(0,3,flag)", "3");
    assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), before);
    assert!(!exec_one(&mut rt, "sum(0,3,flag) = 3").is_failed());
    assert!(!exec_one(&mut rt, "product(1,3,flag) = 1").is_failed());
    assert!(!exec_one(&mut rt, "finite_set_sum({1/3,2/3},flag) = 2").is_failed());
    assert!(exec_one(&mut rt, "sum(0,3,flag) = 4").is_failed());
}
```

Observed failure excerpt:

```text
thread 'execute::execute_eval_stmt::exec_eval_stmt_tests::aggregate_algorithm_terms_keep_checked_equations_and_eval_stores_empty' (71852521) panicked at src/execute/execute_eval_stmt/exec_eval_stmt_tests.rs:257:5:
assertion failed: !exec_one(&mut rt, "sum(0,3,flag) = 3").is_failed()
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::execute_eval_stmt::exec_eval_stmt_tests::aggregate_algorithm_terms_keep_checked_equations_and_eval_stores_empty -- --exact --nocapture
```

## eval_factorial_sqrt_log_closed_numeric_succeed

Primary label: `trust` (test/public-result expectation review; no incorrect mathematics demonstrated).

Repair ownership: local Rust test/expectation work after confirming the public contract. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn eval_factorial_sqrt_log_closed_numeric_succeed() {
    let mut runtime = runtime_with_file_env();
    assert_eval_number(&mut runtime, "eval 2!", "2");
    assert_eval_number(&mut runtime, "eval 3!", "6");
    assert_eval_number(&mut runtime, "eval sqrt(4)", "2");
    assert_eval_number(&mut runtime, "eval sqrt(0.36)", "0.6");
    assert_eval_number(&mut runtime, "eval log(2, 8)", "3");
}
```

Observed failure excerpt:

```text
thread 'execute::execute_eval_stmt::exec_eval_stmt_tests::eval_factorial_sqrt_log_closed_numeric_succeed' (71852540) panicked at src/execute/execute_eval_stmt/exec_eval_stmt_tests.rs:40:22:
expected number 0.6, got ArithmeticOperator(Div(Div { left: Literal(Number(Number { normalized_value: "3" })), right: Literal(Number(Number { normalized_value: "5" })) }))
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::execute_eval_stmt::exec_eval_stmt_tests::eval_factorial_sqrt_log_closed_numeric_succeed -- --exact --nocapture
```

## aggregate_symbolic_reindex_contract

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn aggregate_symbolic_reindex_contract() {
    let mut rt = runtime_with_file_env();
    assert!(!exec_one(&mut rt, "have f fn(k Z) R").is_failed());
    let code = "forall a,b,t Z:\n    a<=b\n    a+t<=b+t\n    =>:\n        sum(a,b,fn(k Z) R {f(k+t)})=sum(a+t,b+t,f)";
    let outcome = exec_one(&mut rt, code);
    assert!(
        !outcome.is_failed(),
        "{}",
        crate::json_output::project_stmt_detailed(&outcome, &rt).stringify_pretty()
    );
    assert!(!exec_one(&mut rt, "have n N+").is_failed());
    assert!(!exec_one(
        &mut rt,
        "forall:\n    3 <= n+2\n    =>:\n        sum(1,n,fn(k Z) R {f(k+2)}) = sum(3,n+2,f)"
    )
    .is_failed());
}
```

Observed failure excerpt:

```text
thread 'execute::execute_eval_stmt::exec_eval_stmt_tests::aggregate_symbolic_reindex_contract' (71852534) panicked at src/execute/execute_eval_stmt/exec_eval_stmt_tests.rs:160:5:
{
  "success": false,
  "kind": "fact",
  "statement": "forall a, b, t Z:\n    a <= b\n    a + t <= b + t\n    =>:\n        sum(a, b, fn (k Z) R{f(k + t)}) = sum(a + t, b + t, f)",
  "verify": {
    "type": "forall",
    "success": false,
    "phase": "search_proof",
    "fact": "forall a, b, t Z:\n    a <= b\n    a + t <= b + t\n    =>:\n        sum(a, b, fn (k Z) R{f(k + t)}) = sum(a + t, b + t, f)",
    "introduced_params": {
      "param_type_well_defined": [
        {
          "type": "obj",
          "well_defined": {
            "success": true,
            "proof": {
              "type": "by_def",
              "family": "StandardSet",
              "kind": "StandardSet",
              "obj": "Z"
            }
          }
        }
      ],
      "defined_params": {
        "stores": [
          {
            "fact_id": "f8"
          },
          {
            "fact_id": "f9"
          },
          {
            "fact_id": "f10"
          }
        ],
        "infers": []
      }
    },
    "assumed_dom_facts": [
      {
        "well_defined": {
          "type": "atomic_except_equality",
          "proof": {
            "well_defined_of_each_parameter": [
              {
                "type": "by_def",
                "family": "Identifier",
                "kind": "Identifier",
                "obj": "a"
              },
              {
                "type": "by_def",
                "family": "Identifier",
                "kind": "Identifier",
                "obj": "b"
              }
            ],
            "predicate_signature": {
              "type": "builtin"
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::execute_eval_stmt::exec_eval_stmt_tests::aggregate_symbolic_reindex_contract -- --exact --nocapture
```

## eval_non_square_sqrt_soft_fails

Primary label: `trust` (test/public-result expectation review; no incorrect mathematics demonstrated).

Repair ownership: local Rust test/expectation work after confirming the public contract. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn eval_non_square_sqrt_soft_fails() {
    let mut runtime = runtime_with_file_env();
    let outcome = exec_one(&mut runtime, "eval sqrt(2)");
    match outcome {
        ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Failed(
            ExecEvalStmtFailed::EvaluationFailed,
        ))) => {}
        other => panic!(
            "expected EvaluationFailed for sqrt(2), failed={}",
            other.is_failed()
        ),
    }
}
```

Observed failure excerpt:

```text
thread 'execute::execute_eval_stmt::exec_eval_stmt_tests::eval_non_square_sqrt_soft_fails' (71852542) panicked at src/execute/execute_eval_stmt/exec_eval_stmt_tests.rs:341:18:
expected EvaluationFailed for sqrt(2), failed=false
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::execute_eval_stmt::exec_eval_stmt_tests::eval_non_square_sqrt_soft_fails -- --exact --nocapture
```

