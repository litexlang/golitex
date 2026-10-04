# src basic audit: tests/unit/execute/induction_repairs/tests.rs

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

## induction_goal_wd_uses_the_induction_domain_without_ih

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn induction_goal_wd_uses_the_induction_domain_without_ih() {
    for keyword in ["induc", "strong_induc"] {
        check(
            &format!("have fn f(x N) N = x\nby {keyword} n from 0:\n    ? f(n) = f(n)\n"),
            &[true, true],
        );
        check(
            &format!("have fn f(x N) N = x\nby {keyword} n from -1:\n    ? f(n) = f(n)\n"),
            &[true, false],
        );
        check(
            &format!("by {keyword} n from 0:\n    ? n / n = n / n\n"),
            &[false],
        );
        check(
            &format!("by {keyword} n from 0.5:\n    ? n = n\n"),
            &[false],
        );
    }
}
```

Observed failure excerpt:

```text
thread 'execute::induction_repair_tests::induction_goal_wd_uses_the_induction_domain_without_ih' (71852711) panicked at src/execute/../../tests/unit/execute/induction_repairs/tests.rs:22:5:
assertion `left == right` failed: have fn f(x N) N = x
by induc n from 0:
    ? f(n) = f(n)

  left: [true, false]
 right: [true, true]
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::induction_repair_tests::induction_goal_wd_uses_the_induction_domain_without_ih -- --exact --nocapture
```

## induction_examples_cover_the_maintained_acceptance_sources

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn induction_examples_cover_the_maintained_acceptance_sources() {
    for path in [
        "examples/stmt_nodes/definition/inductive_nested_cases.lit",
        "examples/stmt_nodes/definition/template_inductive_arithmetic.lit",
        "examples/stmt_nodes/by/induction_domain_and_proof_actions.lit",
        "examples/stmt_nodes/by/induction_collection_binders.lit",
    ] {
        let source =
            std::fs::read_to_string(std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(path))
                .unwrap();
        let mut rt = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        });
        let run = rt.run_litex_code(&source).unwrap();
        assert!(
            run.success && run.session_error.is_none(),
            "{path}: {:?}",
            run.session_error
        );
        assert!(
            run.statement_results.iter().all(|s| !s.is_failed()),
            "{path}"
        );
    }
}
```

Observed failure excerpt:

```text
thread 'execute::induction_repair_tests::induction_examples_cover_the_maintained_acceptance_sources' (71852709) panicked at src/execute/../../tests/unit/execute/induction_repairs/tests.rs:321:9:
examples/stmt_nodes/by/induction_domain_and_proof_actions.lit: None
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib execute::induction_repair_tests::induction_examples_cover_the_maintained_acceptance_sources -- --exact --nocapture
```

