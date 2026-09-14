# Locked premise: name is identity

Status: **locked** (new_pipeline)

## Premise

At any time, a surface name denotes **one** symbol identity for the whole
session:

- Plain `y` is always that same `y`.
- `mod::y` is always that same `mod::y` (distinct from plain `y`).
- Reusing the letter after a binder scope ends is **letter reuse**, like on
  paper: stored AST may still contain binder spelling `y`, and a later
  `have y` is the same name identity, not a second binding instance.

## Hard rules that make this sound

1. **No shadowing.** An inner scope must not occupy a name still visible
   outside (`occupy` only).
2. **No same-name nesting.** Forms such as `{x R: … {x R: …}}` are forever
   forbidden; nested binders must use different names.
3. Therefore at most one **live** binding of a given `OccupiedName` exists.
4. Cache / known-fact keys may treat IR spellings that use the same name as
   the same symbol. Sequential `forall x` / `{x R: …}` with the same binder
   spelling are intended to share identity for lookup.

## What this is not

- It does **not** give alpha-equivalence across renames: `forall x` and
  `forall a` remain different IR keys unless a separate alpha pass exists.
- It does **not** remove `FactId` (proof citation identity) or module
  qualification (`OccupiedName` / `IdentifierWithMod`).
- Exported open terms that mention a local name still need the usual
  claim/export discipline; that is independent of this premise.

## Consequence for `IdentifierId`

Under this premise, **`IdentifierId` was removed** from new_pipeline AST and
runtime id allocation. Symbol identity and IR cache keys use the name
(plain or `mod::name`) only.

`FactId` (proof citation) and module qualification (`OccupiedName` /
`IdentifierWithMod`) remain.

## Discipline required of verifier code

- Instantiate and substitute by binder structure, not by “replace every node
  with this name/id globally” across binder boundaries.
- Prefer full-fact IR for `ByCache`; do not index binder-internal open scraps
  as if they were ambient free terms. Exact `FactIR` ByCache now indexes every
  closed `Fact` shape (including `forall`).
