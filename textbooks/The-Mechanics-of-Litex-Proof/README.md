# The Mechanics of Litex Proof

> **Development status:** This module is developed in public and may contain
> work at different maturity levels. Its presence in the repository is not a
> completion claim; the verification evidence, explicit `trust` boundaries,
> and known limitations below describe what is currently established.

This directory is the canonical Litex module for *The Mechanics of Litex
Proof*. Its workspace is registered in `scripts/.textbooks`. The ordered
exports in [`litex.config`](litex.config) load the preface, shared citation
surface, and Chapters 0--10; no second draft or publication tree is maintained.

Build and verify the complete module with the release binary:

```text
cargo build --release
target/release/litex -compact -runner -r scripts/The-Mechanics-of-Litex-Proof/textbook
```

For an individual registered chapter, use:

```text
target/release/litex -compact -runner -f scripts/The-Mechanics-of-Litex-Proof/textbook/chapter09-sets.lit
```

As of 2026-08-01, Chapters 0--10 pass the complete release project gate. The
executable module contains no `trust`, `axiom`, or `abstract_prop` statement.
The project still imports `std/basics`; the ordinary non-strict project runner
reports that configured imports and earlier exports are loaded through its
trusted-prefix mode.

## Proof boundary used by the book

Atomic proof search follows a visible order:

1. an already-known non-forall atomic fact;
2. deterministic builtin computation or one direct builtin rule;
3. a structural builtin strategy;
4. an applicable known forall visible in the current runtime;
5. a user-defined strategy.

A direct builtin rule does not recursively call another direct rule. A builtin
rule premise may use a known non-forall fact or deterministic computation. A
builtin strategy may descend through a strictly smaller constructor shape;
each immediate child is checked first as a known fact or computation and then
with one fresh direct rule before further structural decomposition.

The corresponding source interfaces are:

- `by def` introduces a positive defined predicate after its mathematical body
  has been proved. Negative predicates continue to use ordinary proofs such as
  `by contra`.
- When a concrete predicate's whole body is one positive ordinary `exist` fact,
  `obtain k from $p(args)` and `witness $p(args) from value` cross that named
  boundary directly at runtime. Named construction excludes `exist!`, which
  uses explicit `witness exist! ...` plus `by def`. Raw existentials, abstract
  predicates, nested local definitions, and multi-clause definitions also keep
  their explicit forms.
- `by thm <builtin-name>(...)` invokes a named semantic object rule, such as
  `set_builder_member` or `tuple_equal_from_coordinates`. These interfaces are
  not silently included in automatic atomic search.
- A nested function application is unfolded one function definition at a time.
  The carrier of an immediate compound argument is stated before evaluation
  when the domain check needs it as a known leaf.
- Automatic known-forall instantiation uses the candidates visible in the
  current runtime, which may include earlier exports or referenced imported
  modules. Use qualified `by thm` when the dependency should be explicit or
  automatic matching does not supply the intended instance; a local claim may
  deliberately turn that result into a nearby reusable forall.
- `let name = value` is used for a proof-local equality alias when the value's
  carrier need not be established separately. Keep typed `have` when its
  carrier fact is part of the proof, especially for products, sets, and
  iterated objects.
- A witness may omit its indented body when the substituted existential body is
  already known. Chapter 8 exposes `inverse_implies_bijective` and
  `bijective_implies_has_inverse`; examples that check both inverse equations
  reuse the first theorem instead of reopening injectivity and surjectivity.

The mathematical rationale and dependency map live in
[`math_collections.md`](math_collections.md). Iteration evidence is kept outside
the shipping module in
`scripts/The-Mechanics-of-Litex-Proof/experience/proof_journals/`.

## Editing workflow

For proof iteration, start one persistent release session before the current
registered file and submit literal outermost `try:` blocks:

```text
target/release/litex -compact -session -before \
  scripts/The-Mechanics-of-Litex-Proof/textbook/chapter10-relations.lit
```

Record materially distinct failures and the accepted replacement in the
chapter's JSON proof journal. Materialize accepted source without the outer
`try:` wrapper, then finish with a clean release `-f` and the complete release
`-r` gate. Keep working records in the owning workspace, outside `textbook/`.
