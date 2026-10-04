# tooling: current boundaries

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: tooling restriction and tooling observations.
- Related workspace: golitex.

These tooling observations are separate from the original K-number inventory;
each dated item retains its actual status and execution boundary.

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

## Conversation retest — 2026-10-04

Task: fresh audit requested by the maintainer. File-output consumption and
mounted hard-error forwarding are now closed local category-2 repairs; see
the [finished experience](../../experience/problem_notes/conversation_retest_local_repairs_2026-10-04.md).
Eighteen tooling tests pass. A removed graph CLI is no longer used by the
textbook file consumer, and actual InternalBug errors survive `-f`/`-r` mounting.

Current status, after the maintainer's clarification:

- `kernel_problem`, closed: strict now rechecks dependency sources, so ordinary
  caches cannot replay trusted false theorems. Direct/transitive rejection,
  valid strict imports and ordinary cache hits pass their unchanged controls.
  [Exact module and fixed regression](../../../module_manager/strict_cache_policy/README.md).
- `trust`, testing work: full collector inventory and correct fence expectations
  still need maintenance. The earlier frozen scan has 871 matched phase examples and
  225/225 formal fences; all 111 failing fences in the repeat are historical
  audits. Two shortcut squared-i fences changed outcome from the preceding
  109-failure capture, whose evidence is preserved. They already have an
  accepted explicit-chain solution. No mass skips or negative relabeling.
  Owner: Codex checks actual selection counts, preserves original contexts and
  positive/negative expectations, restores real collectors and runs the full
  gate. The maintainer need not choose a manifest framework. REL02/REL04.

[Acceptance and exact commands](../../../../tests/tooling/acceptance/conversation-closeout-retest-2026-10-04.md).
[Current clarification and fixed strict controls](../../../../tests/tooling/acceptance/conversation-clarifications-2026-10-04.md).

Back to [issue index](../README.md).
