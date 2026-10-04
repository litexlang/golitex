# BR001: valid -e source beginning with minus is rejected

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

Primary label: `kernel_problem`. Repair ownership: category 2, bounded CLI argument validation; no AST/Env/Runtime change needed for diagnosis.

```sh
litex -strict -e '-2 < 0'
```

Observed: launch_error, exit 2, no JSON. The same source through `-f` succeeds.

Current owner:

```rust
fn is_value(token: &str) -> bool {
    !token.is_empty() && !token.starts_with('-')
}
```

Next check: distinguish the value consumed by an explicit `-e` from option positions. Acceptance: negative-leading valid code works, false negative-leading mathematics still rejects, unknown options and missing values retain errors. This audit does not implement the fix.
