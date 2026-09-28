# `json_output`

Projects `ExecStmtResult` trees into user-facing JSON. Does **not** change the
verify/exec IR (Lean replay and detail still read the full tree).

## Detail levels

```rust
pub enum OutputDetail {
    Compact,   // reserved
    Normal,    // current default for all emit paths
    Detailed,  // reserved
}
```

Today every CLI / test emit uses **Normal**. Compact and Detailed stay stubs
until their shapes are designed.

## Normal statement shape (frozen)

Success:

```json
{
  "success": true,
  "statement": "k >= 0",
  "why_verified": {
    "type": "builtin_rule",
    "rule": "FromKnownInNatural",
    "line": 1,
    "cite": "k $in N"
  },
  "stores": ["k >= 0"],
  "infers": []
}
```

Failure:

```json
{
  "success": false,
  "statement": "a > 10",
  "why_failed": { "phase": "search_proof", "goal": "a > 10" },
  "stores": [],
  "infers": []
}
```

Rules:

- `success` is a bool (not `outcome` string).
- `stores` / `infers` / `cite` / `statement` / `goal` use `readable_string`
  (IR with `#id#` wrappers stripped), not raw IR and not `fact_id`.
- Cite may include `line` when the cited fact has a source line; omit `line` if unknown.
- Normal skips WD subtrees.

## Run envelope

```json
{
  "kind": "run",
  "ok": true,
  "target": "eval",
  "path": null,
  "detail": "normal",
  "statement_results": [ /* Normal stmt objects */ ],
  "session_error": null
}
```

## API

- `project_stmt_normal(result, runtime) -> JsonValue`
- `project_run_normal(run, runtime, target, path) -> JsonValue`
- `print_run_outcome_normal(outcome)` — used by new_pipeline launch

Projection needs a live `Runtime` so cite `FactId`s can resolve to
`readable_string` text.
