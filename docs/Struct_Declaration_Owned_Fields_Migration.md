# Struct declaration-owned fields migration

Status: implemented and under final acceptance on 2026-08-19.

## Target language contract

1. `Setting` and `struct` remain separate concepts. No `model` keyword is introduced.
2. After all header parameters are fixed, `&Struct<args>` is one ordinary set: a named, record-shaped subset of its Cartesian carrier.
3. A symbol, binder, template object, struct-typed field, or function result owns named fields only when its own declaration directly names `&Struct<args>`.
4. A later equality or membership fact never adds, changes, or guesses named fields. It may still expose the ordinary positional consequences of membership in the Cartesian carrier.
5. Field access is written only as `value.field`. The former `&Struct{value}.field` surface form is rejected.
6. Functions may return a struct carrier directly, so `make(...).field` is valid. Callable fields and nested directly struct-typed fields compose with the same rule.
7. `unfold value` is expanded during parsing into the fields owned by the declaration, in field order. The former `unfold &Struct{value}` form is rejected.

## Implementation flow

The migration is intentionally one-way:

1. Parse `&Struct<args>` everywhere an ordinary set expression is accepted.
2. At each binder or declaration, record its direct struct carrier by symbol identity. Preserve that mapping when a `Setting`, existential witness, or template expansion creates fresh symbols.
3. Resolve every `.field` postfix only from that direct carrier. For a call, instantiate the function's declared return set first; for a nested field, instantiate the field's declared carrier first.
4. Keep general struct membership structural: infer tuple arity, Cartesian membership, positional projections, and struct filters. Emit named-field facts only when the receiver already owns that exact carrier.
5. Reduce fields and callable fields through checked constructors and materialized template definitions. Do not search arbitrary equality classes to invent ownership.
6. Expand `unfold` before verification, then run the ordinary arity, carrier, and domain checks on the expanded arguments.
7. Reject removed explicit-selection syntax with a migration-specific diagnostic.

## Source migration procedure

For each old `&S{value}.field` occurrence:

1. Inspect the declaration of `value` rather than only its known facts.
2. If the declaration directly names `&S`, rewrite it to `value.field`.
3. If it does not, introduce a new declaration such as `have value2 &S = (...)` and use `value2.field`; do not translate the old view mechanically.
4. Split proof chains where the old view triggered an incidental equality rewrite. State the object-definition equality and argument congruence as separate checked steps.
5. Add no migration-only `trust`.
6. Run a direct release gate on every changed canonical chapter, then the workspace gate, and record any earlier unchanged baseline blocker separately.

## Documentation and textbook inventory

Updated public documentation:

- `docs/Manual.md`
- `docs/FAQ.md`
- `docs/cheatsheet.md`
- `docs/Examples.md`
- the two language-feature examples for callable fields and `unfold`

Updated canonical textbook workspaces:

- `scripts/Analysis2/textbook`: 80 field selections in `chapter04-power-series.lit`, plus `math_collections.md` and an acceptance note.
- `scripts/linear_algebra_done_right/textbook`: 320 field selections in 22 active chapters, plus `README.md`, `math_collections.md`, and an acceptance note.
- `scripts/mathematics_in_litex/textbook`: 648 field selections in chapters 06, 07, 08, and 10, plus `README.md`, `math_collections.md`, and an acceptance note.

Updated active non-textbook examples include the affected MATH500 complex-number files, the high-school complex interface and its required-2 struct section, and the Setting struct-carrier tracer.

The top-level `textbooks/` directory is a legacy duplicate rather than the registered canonical source. Its five remaining old-syntax files should be regenerated from the canonical `scripts/<workspace>/textbook` sources or removed as legacy data; they should not be hand-maintained in parallel. Historical `probes/` and `session_records/` intentionally retain old syntax as migration evidence.
