# `json_output`

Projects `ExecStmtResult` trees into user-facing JSON. Does **not** change the
verify/exec IR (Lean replay and detail still read the full tree).

## Detail levels

```rust
pub enum OutputDetail {
    Compact,   // reserved
    Normal,    // current default for all emit paths
    Detailed,  // field-isomorphic projection (L2 local_env, T1 no search_trace)
}
```

Default CLI / test emit uses **Normal**. **Detailed** is temporarily a
Normal fallback while the IR projector under `project_detailed/` is realigned
to current Exec/Verify types (`project_stmt_detailed` /
`project_run_detailed` / `emit_run_detailed` still exist as entry points).
Compact stays reserved.

## Normal statement shape (frozen)

Success:

```json
{
  "success": true,
  "statement": "1 + 2 = 3",
  "why_verified": {
    "type": "builtin_rule",
    "rule_name": "Calculation",
    "message": "Both sides evaluate to the same number"
  },
  "stores": ["1 + 2 = 3"],
  "infers": []
}
```

Chinese session (`-lang zh`): same shape with **localized field names** and
localized `rule_name` / `message` values. Example:

```json
{
  "成功": true,
  "语句": "1 + 2 = 3",
  "证明方法": {
    "类型": "builtin_rule",
    "规则名": "计算",
    "说明": "两边都算出同一个数"
  },
  "存储": ["1 + 2 = 3"],
  "推断": []
}
```

`type` *values* (e.g. `builtin_rule`) stay English stable tokens. Key remapping
lives in `json_keys.rs` (`localize_key`); authors always write English keys in
code and `object(lang, …)` remaps them.

Cited-membership example:

```json
{
  "success": true,
  "statement": "k >= 0",
  "why_verified": {
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
- Atomic builtin path: `rule.rule_id_and_message(lang)` on
  `AtomicExceptEqualityFactSearchProofByBuiltinRule` (family enums / leaf
  proofs implement the method under `explain/atomic_builtin_rule/`). Projection
  does not hardcode rule-id strings. Equality uses the same method shape on
  `EqualitySearchProofByBuiltinRule`.
- All Chinese/English copy lives under `json_output/explain/` — verify/exec IR
  stays language-free. `OutputLanguage` comes from `LaunchCommand` (`-lang`).
- Priority of explain coverage:
  1. **English-first:** every Normal surface should have a complete English
     `rule_name` + `message`. Chinese uses the same hooks (`OutputLanguage`,
     `bilingual_*`) and falls back to English until a translation is filled.
  2. `equality_calculation` — full EN/ZH
  3. `equality_builtin` — every equality variant has English copy (+ ZH `None`
     slots)
  4. `atomic_common` — hot atomic membership/order rules (EN + ZH where done)
  5. `stmt_why` + `project_stmt_catalog` — all stmt branches; by/thm/claim carry
     stores when the exec result provides them
  6. remaining Chinese copy is gradual (do not block English completeness)
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
## API

- `project_stmt_normal` / `project_run_normal` / `emit_run_normal`
- `project_stmt_detailed` / `project_run_detailed` / `emit_run_detailed`

Projection needs a live `Runtime` so cite `FactId`s can resolve to
`readable_string` text.
