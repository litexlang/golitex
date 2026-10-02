# Stored atomic citation under known_only: recheck

Task: maintainer requests repair-plan classification and current remaining problems on 2026-10-02.
Scope: the statement suite's supplemental Rust verifier control in golitex.
Status: the formerly failing exact control now passes; stale open record removed. Cause and repair attribution remain unconfirmed.

The existing [Rust test](../../../../tests/unit/execute/builtin_entry_policy/tests.rs) executes `have x R` and `trust x >= 1`, then checks the stored fact under the restricted state:

```rust
assert!(
    !verify(
        &mut rt,
        "x >= 1",
        VerifyState::top_level().known_only_no_wd()
    )
    .is_failed()
);
```

```bash
cargo test --release --lib stored_facts_and_zero_depth_strategy_calculation_remain_available
```

Current result: exit 0, 1 passed, 0 failed. This test also keeps zero-depth strategy arithmetic usable and rejects the unchecked `0 < x + x` goal. The ordinary CLI control `have x R; trust x >= 1; x >= 1` passes its three statements; the CLI cannot select the internal VerifyState and is not a substitute for the Rust control. The setup's trust is part of the stored-citation test; it does not discharge K005 or any unresolved goal.

The [classification/recheck journal](../../proof_journals/stmt_repair_plan_classification_2026-10-02.json) preserves the removed README and its original 6-passed/1-failed capture, plus current native outputs and the exact Rust result. This task changed skills/plans, not production Rust. Concurrent workspace changes prevent attributing this success to a particular repair. Only the formerly failing test was rerun; the entire seven-test policy gate was not reaccepted here.
