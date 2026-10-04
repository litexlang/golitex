# src basic audit: src/execute/order_stage_a_remainder_tests.rs

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

## order_stage_a_finite_set_size_union_and_surjection

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn order_stage_a_finite_set_size_union_and_surjection() {
    let mut runtime = runtime_with_file_env();
    assert!(
        !exec_one(&mut runtime, "trust $is_finite_set(union({1}, {2}))").is_failed()
    );
    assert!(
        !exec_one(
            &mut runtime,
            "finite_set_size(union({1}, {2})) <= finite_set_size({1}) + finite_set_size({2})"
        )
        .is_failed(),
        "union card <= sum"
    );

    let mut runtime = runtime_with_file_env();
    assert!(!exec_one(&mut runtime, "have A set = {1, 2}").is_failed());
    assert!(!exec_one(&mut runtime, "have B set = {1}").is_failed());
    assert!(!exec_one(&mut runtime, "have fn f(x A) B = 1").is_failed());
    assert!(!exec_one(&mut runtime, "trust $surjective(A, B, f)").is_failed());
    assert!(
        !exec_one(&mut runtime, "finite_set_size(B) <= finite_set_size(A)").is_failed(),
        "surjection codomain card <= domain"
    );
}
```

Observed failure excerpt:

```text
thread 'execute::order_stage_a_remainder_tests::order_stage_a_finite_set_size_union_and_surjection' (71852893) panicked at src/execute/order_stage_a_remainder_tests.rs:179:5:
union card <= sum
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::order_stage_a_remainder_tests::order_stage_a_finite_set_size_union_and_surjection -- --exact --nocapture
```

