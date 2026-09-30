# `json_output`

Projects `ExecStmtResult` trees into user-facing JSON. Does **not** change the
verify/exec IR (Lean replay and detail still read the full tree).

## Detail levels

```rust
pub enum OutputDetail {
    Compact,   // thin: success + statement (+ fail_reason)
    Normal,    // current default for all emit paths
    Detailed,  // field-isomorphic projection (L2 local_env, T1 no search_trace)
}
```

Default CLI / test emit uses **Normal**. **Compact** is implemented under
`project_compact/` (`project_stmt_compact` / `project_run_compact` /
`emit_run_compact`). **Detailed** is temporarily a Normal fallback while the
IR projector under `project_detailed/` is realigned.

## Compact statement shape

Success — only disposition + source text:

```json
{
  "success": true,
  "statement": "1 + 2 = 3"
}
```

Failure — add a thin `fail_reason` (`phase` + optional `goal`):

```json
{
  "success": false,
  "statement": "a > 10",
  "fail_reason": {
    "phase": "search_proof",
    "goal": "a > 10"
  }
}
```

Chinese (`-lang zh`):

```json
{
  "成功": true,
  "语句": "1 + 2 = 3"
}
```

```json
{
  "成功": false,
  "语句": "a > 10",
  "失败原因": {
    "阶段": "搜索证明",
    "目标命题": "a > 10"
  }
}
```

Compact deliberately omits `proof_method`, `stores`, `infers`, and cite details.
Field order: `success` → `statement` → (`fail_reason` when failed).

## Normal statement shape (frozen)

Success:

```json
{
  "success": true,
  "statement": "1 + 2 = 3",
  "proof_method": {
    "type": "builtin_rule",
    "rule_name": "Calculation",
    "message": "Both sides evaluate to the same number"
  },
  "stores": ["1 + 2 = 3"],
  "infers": []
}
```

Chinese session (`-lang zh`): same shape with **localized field names** and
localized `type` / `phase` / `rule_name` / `message` values (no English tokens
under Chinese keys). Example:

```json
{
  "成功": true,
  "语句": "1 + 2 = 3",
  "证明方法": {
    "类型": "内置规则",
    "规则名": "计算",
    "说明": "两边都算出同一个数"
  },
  "存储": ["1 + 2 = 3"],
  "推断": []
}
```

Key remapping lives in `json_keys.rs` (`localize_key`); authors always write
English keys in code and `object(lang, …)` remaps them. Under `-lang zh`,
emitted `类型` / `阶段` *values* are Chinese too (owned by explain/helper
match arms).

Cited-membership example:

```json
{
  "success": true,
  "statement": "k >= 0",
  "proof_method": {
    "type": "builtin_rule",
    "rule_name": "From known in N",
    "message": "The goal follows from a known natural-number membership",
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
- Builtin why: print `rule_name` + `message` only (no `rule` / `rule_id` /
  `variant` in Normal JSON). Stable ids live inside `explain/` for tests.
- Builtin why path: call `rule.rule_id_and_message(lang)` only.
  - Atomic: `explain/atomic_builtin_rule/` — every family enum and every leaf
    proof has dedicated EN+ZH copy (no family-level stubs).
  - Equality: `explain/equality_builtin_rule/` (top enum dispatches to each
    leaf; every leaf + Calculation has EN+ZH).
  Projection never matches on rule variants for copy text.
- Non-builtin searched-proof routes (`builtin_strategy`, `by_definition`,
  `equivalence_class`, …) use `explain/searched_proof_why.rs` so they also
  emit `rule_name` + `message` (not a bare `type` tag).
- All Chinese/English copy lives under `json_output/explain/` — verify/exec IR
  stays language-free. `OutputLanguage` comes from `LaunchCommand` (`-lang`).
- Priority of explain coverage:
  1. Every Normal surface has English + Chinese `rule_name` / `message`
     (stmt kinds, compound facts, searched-proof routes, equality leaves,
     every atomic builtin leaf, Calculation).
  2. Detailed remains a Normal fallback until its IR projector is finished.
- `stores` / `infers` / `cite` / `statement` / `goal` use `readable_string`
  (IR with `#id#` wrappers stripped), not raw IR and not `fact_id`.
- Cite may include `line` when the cited fact has a source line; omit `line` if unknown.
- Normal skips WD subtrees.

## Detailed statement shape (frozen contract)

Same envelope as Normal run JSON, but `"detail": "detailed"`.

Each statement projects the **result IR fields** (not search noise, T1):

- `success`, `kind`, `statement`
- `verify`: full recursive VerifyFactResult (includes WD + winning `searched_proof`)
- `store_and_infer`: `{ stores, infers }` entries with `fact_id` + readable `fact`
- binder `local_env`: **L2 summary** only (`identifiers`, `facts`, `well_defined`)

Does **not** include failed search attempts / `search_trace`.

Fact success sketch:

```json
{
  "success": true,
  "kind": "fact",
  "statement": "k >= 0",
  "verify": {
    "type": "atomic_except_equality",
    "success": true,
    "fact": "k >= 0",
    "well_defined": { "...": "..." },
    "searched_proof": {
      "type": "builtin_rule",
      "family": "GreaterEqualFact",
      "rule": "FromKnownInNatural",
      "cite_fact_id": "f1",
      "cite": "k $in N"
    }
  },
  "store_and_infer": {
    "stores": [{ "fact_id": "f2", "fact": "k >= 0" }],
    "infers": []
  }
}
```

## Run envelope

```json
{
  "kind": "run",
  "success": true,
  "target": "eval",
  "path": null,
  "detail": "normal",
  "language": "en",
  "statement_results": [ /* Normal or Detailed stmt objects */ ],
  "session_error": null
}
```

`language` is `en` or `zh` from `-lang` (default `en`). Builtin `rule_name` /
`message` follow this language via `json_output/explain/`.

## Acceptance (Normal + Compact)

Locked by `cargo test --lib json_output::` (`acceptance_tests` +
`project_normal_tests` + `project_compact_tests`):

1. **Normal success shape / field order**: `success` → `statement` →
   `proof_method` → `stores` → `infers`
2. **Normal failure shape**: `success: false` → `statement` → `why_failed` →
   empty `stores`/`infers`
3. **Compact success**: only `success` + `statement` (no proof_method/stores/infers)
4. **Compact failure**: `success` → `statement` → `fail_reason` (`phase` +
   optional `goal`)
5. **Builtin why (Normal)**: `type` + `rule_name` + `message` only (no `rule` /
   `rule_id` / `variant`)
6. **Cite (Normal)**: readable string, no `#id#` wrappers; optional `line`
7. **Chinese (`-lang zh`)**: field keys remapped; type/phase/rule text Chinese
8. **Stmt kinds**: every catalog kind has bilingual `explain_stmt_kind`
9. **Equality builtins**: all variants bilingual via `rule.rule_id_and_message(lang)`
10. **Searched-proof routes / compound facts**: bilingual `rule_name` + `message`
11. **Run envelope**: `kind` / `success` / `detail` (`normal`|`compact`) /
    `language` / `statement_results`

**Out of this acceptance gate:** Detailed projector still falls back to Normal
until realigned.

## API

- `project_stmt_compact` / `project_run_compact` / `emit_run_compact`
- `project_stmt_normal` / `project_run_normal` / `emit_run_normal`
- `project_stmt_detailed` / `project_run_detailed` / `emit_run_detailed`

Projection needs a live `Runtime` so cite `FactId`s can resolve to
`readable_string` text.
