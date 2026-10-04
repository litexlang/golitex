# Object audit: fn_set

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

Primary label: `trust` (positive-fixture/public-signature expectation drift; no kernel defect established). Repair ownership: provisional, diagnosing; check explicit existing proof paths before proposing local Rust work. Escalate before changing shared policy or protected state/AST.

## P04

Original fixture: `examples/test_objs/fn_set.lit`.

```litex
sketch:
    let F = fn(x R) x
    $is_set(F)
```

Observed: exit 1, success False, session_error Runtime(ParseError(RuntimeParseError { message: "undefined name `x`", line: 2, path: Eval })).

```json
{
  "kind": "run",
  "success": false,
  "target": "eval",
  "path": null,
  "detail": "normal",
  "language": "en",
  "statement_results": [],
  "session_error": "Runtime(ParseError(RuntimeParseError { message: \"undefined name `x`\", line: 2, path: Eval }))"
}
```

Boundary: dependent function signatures are explicitly rejected by the current parser contract. Do not restore them merely to satisfy this older positive fixture; review the fixture expectation.

Next/acceptance: reproduce the exact mathematical goal with the original scope; inspect WD versus search versus context/output failure; repair only after preserving the nearest false, domain and scope controls.
