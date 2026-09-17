# Identifier identity (new_pipeline)

Status: **current** — plain atoms carry `IdentifierId`.

Canonical note for symbol identity, binder discipline, IR keys, and known-*
indexing.

## Owners

| Area | Path |
|------|------|
| Parse occupy / resolve | `parse/`, `runtime::ParseScope` |
| Plain refs | `IdentifierObj::Plain { id, name }` |
| Qualified refs | `WithExportFileId` / `WithModAndExportFileId` (no id) |
| Binder / param slots | `BoundName { id, name }` |
| IR / display | `display_and_ir/` — plain IR `#id#name`, display = surface name |
| Def table | `DefinitionMemory.identifiers: HashMap<PlainName, …>` (by name, not id) |
| Fact store | `facts_by_id` + known-equality / known-atomic (linear) / known-forall |
| Instantiate | `instantiate/` — subst key = `IdentifierId` |

## Contract

1. **Allocate at parse.** `define_plain_atom` → `BoundName` with a fresh
   `IdentifierId`. Re-opening binders uses `occupy_bound_name` (same id).
2. **Resolve plain refs.** Free `x` becomes `IdentifierObj::Plain` with the
   visible scope id. Undefined plain name → parse error.
3. **Qualified names** have no `IdentifierId`; identity is the qualified
   `AtomicName` indices + name. They are not stored in `ParseScope`.
4. **No shadowing.** Same-name nested binders stay forbidden (occupy fence).
5. **Letter reuse.** After a scope ends, a later `have x` gets a **new** id.
6. **IR.** Plain → `#<id.value>#<name>` (e.g. `#3#x`). Display → `x` only.
   Qualified IR unchanged (`f0::name` / `m0::f1::name` style placeholders).
7. **Instantiate** keys by `IdentifierId`. No `fresh` / `□N` capture rename.
8. **Single-body binder objs.** `SetBuilder` / `FnSet` / `AnonymousFn` have one
   body (no `surface`/`alpha` dual). `alpha_normalize` is **removed for now**.
9. **Forall / exact IR.** Two source-identical `forall x …` may get different
   binder ids and different IR. Exact IR miss is **accepted**; prove via
   instantiate / other paths, not whole-fact IR equality.
10. **known-atomic (non-equality).** Bucket by `(prop, polarity)`, linear scan
    by equality-class (`ObjIR`); each arg justified by proving
    `known_arg = goal_arg` via equality search with forall/rewrite off.
11. **known_equality** stays a graph + equivalence classes keyed by `ObjIR`.

## Definition table vs IdentifierId

The definition table stores definitions under the **surface plain name**.
Occurrence identity for objects/facts uses `IdentifierId` on AST/IR.
Looking up “what is `x` defined as?” is by name; substituting / matching
free `x` in a term is by id.

## Deferred

- **Alpha equality for set builders** (`{x: P} = {y: P}` as a dedicated rule)
  will need something like `alpha_normalize` again later. Not in tree now.
- Some stmt-only binder slots (induction / `for`) may still be bare `String`;
  migrate to `BoundName` when those paths are wired.

## Do-not-break checklist

- [ ] Plain IR embeds `#id#name`; display never shows the id wrapper.
- [ ] Qualified atoms never allocate `IdentifierId`.
- [ ] Nested same-name binders remain parse-forbidden.
- [ ] `inst_*` uses `HashMap<IdentifierId, Obj>` only.
- [ ] No `surface`/`alpha` dual fields on binder objs.
- [ ] Non-equality known-atomic stays linear + class filter; equality graph untouched.
- [ ] Obj WD ByKnown still keys by `ObjIR` (which now includes plain ids).
