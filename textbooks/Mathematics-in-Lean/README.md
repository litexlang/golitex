# Mathematics in Lean, Chapters 1–13, in Litex

This runnable Litex project follows the definitions, main mathematical results,
and necessary constructions of all thirteen original chapters of *Mathematics
in Lean*. It preserves source order, collapses repeated Lean tactic
demonstrations, and leaves every unavailable proof or construction visible as
typed `trust` rather than silently changing the mathematics.

The source of truth is the local *Mathematics in Lean* snapshot at commit
`6dfa2c166a410d2f0f278d327ea81ae0fa6d3c32`.

## Run entrypoint

From the `golitex` repository root:

~~~sh
RUST_MIN_STACK=8388608 target/debug/litex -runner -r textbooks/Mathematics-in-Lean -compact
~~~

The project imports `std/basics` and exports `citation`, then `chap1` through
`chap13` in source order. Cross-chapter objects, functions, predicates, and
theorems use explicit module qualification.

## Chapter map

- `chap1`–`chap5`: introductory functions and facts; basic algebra and logic;
  sets/functions; and elementary number theory.
- `chap6`: finite counting, list/tree/formula interfaces, and their
  source-facing induction results.
- `chap7`–`chap9`: records and Gaussian integers; algebraic hierarchies and
  quotients; then groups, rings, ideals, and polynomials.
- `chap10`: vector spaces, linear maps, subspaces and quotients, eigen data,
  matrices, bases, and dimension.
- `chap11`: filters, metric spaces, topological spaces, compactness, and
  sequential results.
- `chap12`: elementary and normed-space differential calculus.
- `chap13`: interval integration, measurable spaces and measures, Bochner
  integration, Fubini, convolution, and change of variables.

`math_collections.md` records the cross-chapter mathematical interfaces; the
source manifest and status ledgers live in `scripts/mathematics_in_litex/`.

## Modeling and trust boundary

- `prop` names a reusable candidate property or relation.
- `have` / `have fn` / `template` introduce an object, callable construction,
  or carrier-dependent construction.
- A closed source assertion is written directly as a fact or a named `thm`.
  Fermat's Last Theorem, for example, is one trusted universal fact, not a
  zero-argument `prop` wrapper.
- When a source theorem is an equivalence that Litex cannot state as a
  top-level theorem result, the chapter records its forward and reverse facts
  separately (for example, `..._forward` and `..._reverse`).
- Every unfinished item has a literal, executable typed `trust` body or typed
  trusted object declaration. A prose line after `trust:` is never treated as
  proof debt or as a proof.

Trust belongs to the smallest source-facing missing proof or construction. It
does not weaken a function into a proposition, turn a fact into a predicate, or
hide an unproved quotient compatibility condition.

## Small use example

After the project prefix has loaded Chapter 1, its callable definition is used
with the explicit module name:

~~~litex
chap1::add_three(2) = 5
~~~

The chapter runner checks this from the defining equation. The trusted Fermat
fact can likewise be specialized directly; it does not require a
`$fermat_last_theorem()` wrapper.
