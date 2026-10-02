# Internal control: stored atomic citation under known_only

Status: needs diagnosis. This is an observed Rust verifier-control failure, not an additional confirmed failure of a native Litex input.
Task: supplemental builtin-policy gate during K010 repair on 2026-10-02.
Scope: Fact verification with `VerifyState::known_only_no_wd()` in golitex.

The [existing Rust test](../../../../../tests/unit/execute/builtin_entry_policy/tests.rs) executes `have x R` and `trust x >= 1`, then asks the verifier to cite `x >= 1` with builtin/deep/rewrite search disabled. Both setup statements succeed, but the stored-fact verification returns a failed result. The control expects stored facts to remain usable under those flags.

```bash
cargo test --release --lib builtin_entry_policy_tests
```

Captured result: 6 passed, 1 failed, exit 101. [observed.json](observed.json) retains the exact test source and failure. The failing test is `stored_facts_and_zero_depth_strategy_calculation_remain_available`.

This reproduction has no finite-list carriers. K010's new finite-membership rule therefore has no source candidate in it. That narrows the investigation but does not establish the cause or a pre-task baseline: the workspace also contains concurrent changes. Do not weaken the test or change proof-search flags merely to make this gate pass.

Next step: compare the stored atomic citation and its argument-equality/WD evidence under ordinary and known-only states, then isolate the baseline in an independent checkout if needed. The example suite's CLI manifest cannot express an internal VerifyState override, so this record is separate from its one remaining native-input gap (K005).

Back to [Fact folder](../README.md) and [issue index](../../README.md).
