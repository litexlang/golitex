# `execute_def_struct_stmt` — status

Scope: `struct Name …:` **definition** execution only.
Related release / membership / parse gaps are listed below because this
module’s own comments point at them.

## Done (definition pipeline)

1. Header typed params: WD + define (`introduce_typed_parameters`, including
   auto-open when a param carrier is `&Struct`).
2. Optional header domain facts: **well-definedness check only** (same as
   legacy def-time check; not stored as live ambient facts after the def).
3. Each field type Obj WD.
4. Nested field scope: define fields with parse-time `BoundName` ids, then
   `<=>:` fact WD under those binders.
5. Store `DefStructStmt` into the parent env (`store_def_struct`).
6. Soft-fail variants: `ParamType`, `AutoOpenStructLayer`, `StructureDomain`,
   `FieldType`, `EquivalentFact`.

Parse (not this module): `new_pipeline` requires **at least two fields**;
0 or 1 field is a parse error. Release has no one-field identity-view path.

## Not implemented here / deferred by design of this module

These are **out of `exec_def_struct_stmt`’s job** (def only checks + stores
the AST definition). Callers / other modules must own them:

| Gap | Where it should live | Notes |
|-----|----------------------|--------|
| Prove `$in &Struct` (opaque membership) | `in_fact` / struct membership builtin | Manual: membership checks tuple carrier + `<=>:` internally **without** storing bridges/laws. **No StructObj branch in new_pipeline `in_fact` builtins yet.** `release struct def` can still succeed when `e $in &Struct` is already known (e.g. after `trust have e &Struct` / direct bind). |
| Non-direct auto-open | already intentional | Only direct `&Struct` binder auto-opens one layer. Function returns, nested fields, equality, later membership still need `release struct def`. |

## Adjacent gaps (not in this folder, but block “full struct”)

| Gap | Location | Notes |
|-----|----------|--------|
| Setting refs inside `struct Name<…>` | parse `def_misc.rs` | Comment: setting refs in `<>` still deferred. |
| `struct Name(...)` paren params | parse | Rejected; Manual wants `<…>` only. |
| Lean / JSON tracers for `ReleaseStructDef` | stmt result / compiler | Exec result type exists; Lean replay still deferred. |

## Wired elsewhere (not this module)

- `release struct def e` → `exec_release_struct_def_stmt` (carrier resolve → prove membership → `release_one_struct_layer`), matched from `exec_stmt`.

## What this module deliberately does **not** do

- Does **not** release tuple bridges, field carriers, or `<=>:` into the parent
  env at definition time (laws live on the stored definition until release /
  auto-open).
- Does **not** prove or store `$in &Struct` for inhabitants.
