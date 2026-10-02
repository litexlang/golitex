# tooling: current boundaries

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: tooling restriction and tooling observations.
- Related workspace: golitex.

These are explicit implementation restrictions, documented policy, or tooling drift. They are not counted among the ten open issue groups. If support is intended, make that decision before changing the existing rejection contract.

### Input: `litex -compact -runner -f file.lit` / `-before` / `-isolated`

- Observed boundary: Current launch parser does not implement the old skill flags.
- Supported route: `litex -f file.lit`, JSON `success`, process exit, and independent `-e` scenarios.
- Captured authoring evidence: [authoring.json](../../proof_journals/authoring.json).

### Input: `try:` candidate wrappers

- Observed boundary: No current parser arm for `try`.
- Supported route: Independent release processes; accepted candidate sources and failures persist in the local journal.
- Captured authoring evidence: [authoring.json](../../proof_journals/authoring.json).

### Examples harness drift

```bash
cargo test --release run_examples
```

No matching harness was found in the inspected current source/test tree. A filtered command returning success with zero tests is not examples coverage. Use the explicit `cargo test --release --test test_statements` target and the local manifest runner. Legacy documentation elsewhere remains outside this organization task.

Malformed initial attempts and unsupported shorthand remain in the chronological journal; they are not silently promoted to confirmed bugs.

Back to [issue index](../README.md).
