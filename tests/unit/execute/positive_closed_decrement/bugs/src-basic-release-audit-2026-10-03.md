# src basic audit: tests/unit/execute/positive_closed_decrement/tests.rs

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

## fibonacci_uses_the_original_two_step_recursive_domain

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn fibonacci_uses_the_original_two_step_recursive_domain() {
    let code = "have fn fib(n Z: n >= 0) R by induc n from 0:\n    case n < 2: 1\n    case n >= 2: fib(n - 2) + fib(n - 1)\nfib(0) = 1\nfib(1) = 1\nfib(2) = fib(2 - 2) + fib(2 - 1)\nfib(2 - 2) = fib(0)\nfib(2 - 1) = fib(1)\nfib(2) = fib(0) + fib(1) = 2\n";
    let run = runtime().run_litex_code(code).unwrap();
    assert!(run.session_error.is_none(), "{:?}", run.session_error);
    assert!(run.success);
}
```

Observed failure excerpt:

```text
thread 'execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::positive_closed_decrement_tests::fibonacci_uses_the_original_two_step_recursive_domain' (71852577) panicked at src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/search_atomic_except_equality_fact_proof_by_builtin_rules/../../../../../../tests/unit/execute/positive_closed_decrement/tests.rs:44:5:
Some(Runtime(ParseError(RuntimeParseError { message: "undefined name `fib`", line: 4, path: Eval })))
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::positive_closed_decrement_tests::fibonacci_uses_the_original_two_step_recursive_domain -- --exact --nocapture
```

