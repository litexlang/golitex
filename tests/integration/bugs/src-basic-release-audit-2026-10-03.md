# src basic audit: tests/integration/test_statements.rs

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

## statement_fixtures_cover_actual_ast_leaves_and_nested_bodies

Primary label: `kernel_problem` (provisional; exact root cause is not yet established).

Repair ownership: provisional, diagnosing; distinguish authoring from bounded Rust behavior before repair. Shared search policy, state lifetime or protected AST/Env changes require maintainer discussion.

Exact executed Rust test:

```rust
fn statement_fixtures_cover_actual_ast_leaves_and_nested_bodies() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(check_fixtures)
        .unwrap()
        .join()
        .unwrap();
}
```

Observed failure excerpt:

```text
thread '<unnamed>' (71854761) panicked at tests/integration/test_statements.rs:64:17:
/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-03/src-basic-release-audit/snapshot/examples/test_statements/def_algo_by_induc_stmt.lit: Fact(AtomicFact(EqualFact(EqualFact { fact_id: FactId(1034), left: FnObj(FnObj { head: Identifier(Plain { id: IdentifierId(1), name: "algo_count" }), body: [[Literal(Number(Number { normalized_value: "1" }))]] }), right: Literal(Number(Number { normalized_value: "0" })), line_file: Some(SourceLine { line: 10, origin: Eval }) })))
note: run with `RUST_BACKTRACE=1` environment variable to display a backtrace

thread 'statement_fixtures_cover_actual_ast_leaves_and_nested_bodies' (71854760) panicked at tests/integration/test_statements.rs:21:10:
called `Result::unwrap()` on an `Err` value: Any { .. }


failures:
    statement_fixtures_cover_actual_ast_leaves_and_nested_bodies

test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.07s

error: test failed, to rerun pass `--test test_statements`
error: 2 targets failed:
    `--lib`
    `--test test_statements`
```

Next check: reproduce this test through the release statement entry, identify the earliest failed obligation or changed output contract, and pair any repair with the closest false/ill-defined control. Acceptance: this exact test and relevant positive/negative caller pass; no weakened goal or trust.

Focused command:

```sh
cargo test --release --lib statement_fixtures_cover_actual_ast_leaves_and_nested_bodies -- --exact --nocapture
```

