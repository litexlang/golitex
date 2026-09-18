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
2. **Resolve plain refs.** Free `x`:
   - bound in **file-root** parse scope (index 0) →
     `IdentifierObj::WithExportFileId` / `WithModAndExportFileId`
     (no id; uses `current_export_file_id` and optional `current_mod_id`);
   - bound in an **inner** scope → `IdentifierObj::Plain { id, name }`.
   Undefined plain name → parse error.
3. **Qualified names** have no `IdentifierId`; identity is the qualified
   `AtomicName` indices + name. They are not stored in `ParseScope`.
4. **Definition store keys** stay **plain** (`have x` / `let x` / `prop P`
   register under `"x"` / `"P"`). Side-effect facts created at exec
   (`let x = 1` stores equality; `have x R` stores type facts) use
   `identifier_obj_for_stored_mention`: file-root → qualified LHS/mention,
   inner → plain.
5. **No shadowing.** Same-name nested binders stay forbidden (occupy fence).
6. **Letter reuse.** After a scope ends, a later `have x` gets a **new** id.
7. **IR.** Plain → `#<id.value>#<name>` (e.g. `#3#x`). Display → `x` only.
   Qualified → `f0::x` / `m0::f1::x` style placeholders.
8. **Instantiate** keys by `IdentifierId`. No `fresh` / `□N` capture rename.
9. **Single-body binder objs.** `SetBuilder` / `FnSet` / `AnonymousFn` have one
   body (no `surface`/`alpha` dual). `alpha_normalize` is **removed for now**.
10. **Forall / exact IR.** Two source-identical `forall x …` may get different
    binder ids and different IR. Exact IR miss is **accepted**; prove via
    instantiate / other paths, not whole-fact IR equality.
11. **known-atomic (non-equality).** Bucket by `(prop, polarity)`, scan same
    arity; each arg justified by proving `known_arg = goal_arg` via equality
    search with forall/rewrite off (includes MatchingOneArgByOne peel).
12. **known_equality** stays a graph + equivalence classes keyed by `ObjIR`.

## Definition table vs IdentifierId

The definition table stores definitions under the **surface plain name**.
Occurrence identity for objects/facts uses `IdentifierId` on plain AST/IR,
or qualified indices+name after file-root promotion.
Looking up “what is `x` defined as?” is by plain name; citing it across
files uses `file::x` / `mod::file::x`.

## Deferred

- **Alpha equality for set builders** (`{x: P} = {y: P}` as a dedicated rule)
  will need something like `alpha_normalize` again later. Not in tree now.
- Some stmt-only binder slots (induction / `for`) may still be bare `String`;
  migrate to `BoundName` when those paths are wired.
- **`have fn` / `by induc` parse** still not wired; when wired, occupy `f` at
  file root first so body free refs to `f` qualify via the same rule.
- **`-r` / project mount run loop** still deferred; set `current_mod_id` +
  `current_export_file_id` before parsing each export file.

## Do-not-break checklist

- [ ] Plain IR embeds `#id#name`; display never shows the id wrapper.
- [ ] Qualified atoms never allocate `IdentifierId`.
- [ ] File-root free refs promote; sketch/inner binders stay Plain.
- [ ] Nested same-name binders remain parse-forbidden.
- [ ] `inst_*` uses `HashMap<IdentifierId, Obj>` only.
- [ ] No `surface`/`alpha` dual fields on binder objs.
- [ ] Non-equality known-atomic stays linear + class filter; equality graph untouched.
- [ ] Obj WD ByKnown still keys by `ObjIR` (which now includes plain ids).
- [ ] Def table keys remain plain; stored mentions of file-root symbols qualify.