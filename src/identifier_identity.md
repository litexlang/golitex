# Identifier identity

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
| Def table | `DefinitionMemory.identifiers: HashMap<PlainName, StoredIdentifierDefinition>` (by name, not id); value carries `(name, stmt)` or scoped `ParamType((BoundName, ParamType))` |
| Fact store | `facts_by_id` + known-equality / known-atomic (linear) / known-forall |
| Instantiate | `instantiate/` — subst key = `IdentifierId` |

## Contract

1. **Allocate at parse.** `define_plain_atom` → `BoundName` with a fresh
   `IdentifierId`. Re-opening binders uses `occupy_bound_name` (same id).
2. **Resolve plain refs.** Free `x`:
   - bound in **outermost** parse scope (index 0) **and** live `CodeSource`
     is `RootExport` / `ImportedExport` →
     `IdentifierObj::WithExportFileId` / `WithModAndExportFileId`
     (no id);
   - bound in outermost scope under `Eval` / `Repl` / `StandaloneFile`, or
     bound in an **inner** scope → `IdentifierObj::Plain { id, name }`.
   Undefined plain name → parse error.
3. **Qualified names** have no `IdentifierId`; identity is the qualified
   `AtomicName` indices + name. They are not stored in `ParseScope`.
4. **Definition store keys** stay **plain** (`have x` / `let x` / `prop P`
   register under `"x"` / `"P"`). Side-effect facts created at exec
   (`let x = 1` stores equality; `have x R` stores type facts) use
   `identifier_obj_for_stored_mention`: outermost + promoting `CodeSource` →
   qualified LHS/mention, else plain.
5. **No shadowing.** Same-name nested binders stay forbidden (occupy fence),
   except a nested parse scope may shadow a live **file-root obtain** binding
   (so `exist k` / `obtain k from exist k` works after an earlier `obtain k`).
   A later `obtain k` may also replace an earlier file-root obtain binding
   (new `IdentifierId` + `source_line` in `obtain_parse_ids`).
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
12. **known_equivalence_classes** stays a graph + equivalence classes keyed by `ObjIR`.
13. **`StructFieldDef.binding`** is `BoundName` (allocated when the field line is
    parsed). `<=>:` free refs reuse that id; exec must not allocate a second
    field id for the field binder scope.

## Definition table vs IdentifierId

The definition table stores definitions under the **surface plain name**.
Stmt payload fields that are definition / store keys (`Def*Stmt.name`,
`HaveFn*Stmt.name`, `DefTemplateStmt.template_name`, obtain `equal_tos`,
`HaveByPreimageStmt.preimage_names`, …) are typed as `PlainName`.
Occurrence identity for objects/facts uses `IdentifierId` on plain AST/IR,
or qualified indices+name after file-root promotion.
Looking up “what is `x` defined as?” is by plain name; citing it across
files uses `file::x` / `mod::file::x`.

## Deferred

- Full `alpha_normalize` rewrite of binder objs is still absent (single body
  only). **Structural alpha equality** for `FnSet` / `SetBuilder` is wired as
  equality builtins (`ByFnSetAlphaEqual` / `ByAnonymousFnAlphaEqual` /
  `BySetBuilderAlphaEqual` / `ByEqualToObjWithFreeParamsLookup`): binders
  may differ; free structure must match. Example: `R -> R = R -> R`,
  `{x R: x > 0} = {y R: y > 0}`. Membership reuse goes through known `$in` +
  arg equality (no dedicated `$in` alpha rule).
- Some stmt-only binder slots (induction / `for`) may still be bare `String`;
  migrate to `BoundName` when those paths are wired.
- **`have fn … = …` / `have …:` (by exist) / `have fn by cases` / `have fn by induc`**
  are wired. Occupy `f` at file root before parsing the body so
  free refs to `f` qualify via the same rule.
  `have fn by exist!` parses goal-only with forall/`exist!` shape checks; exec
  stores `f $in FnSet`, property forall, and uniqueness forall (no EqualToFunction),
  and records `StoredIdentifierDefinition::HaveFnByForallExistUnique` so
  `release obj def` can rebuild those three facts.
  A `template` may run this body under local params; `\Name<args>` installs
  the same three facts (membership / property / uniqueness) on the instance.
- **`-r` / project mount run loop** still deferred for some polish; set
  `Runtime.code_source` (`RootExport` / `ImportedExport` / …) before parsing
  each export or standalone file. `Eval` / `Repl` never pretend to be `f0`.

## Do-not-break checklist

- [ ] Plain IR embeds `#id#name`; display never shows the id wrapper.
- [ ] Qualified atoms never allocate `IdentifierId`.
- [ ] File-root free refs promote only under `RootExport` / `ImportedExport`;
  `Eval` / `Repl` / `StandaloneFile` stay Plain.
- [ ] Nested same-name binders remain parse-forbidden.
- [ ] `inst_*` uses `HashMap<IdentifierId, Obj>` only.
- [ ] No `surface`/`alpha` dual fields on binder objs.
- [ ] Non-equality known-atomic stays linear + class filter; equality graph untouched.
- [ ] Obj WD ByKnown still keys by `ObjIR` (which now includes plain ids).
- [ ] Def table keys remain plain; stored mentions of file-root symbols qualify.