# Sets, Functions, and Relations in a Nutshell

This independent showcase reads like a very small first chapter on sets and
functions. It has one continuous mathematical line instead of a collection of
isolated membership facts:

- compute the union of two finite sets by extensionality;
- use `by enumerate finite_set` to prove that `x |-> x + 1` sends every
  element of `{1, 2, 3}` into `{2, 3, 4}`;
- present that function directly by formula and as an anonymous first-class
  function value;
- represent the successor relation as a subset of `N x N`; and
- prove unique output, select a callable function with `have fn ... by
  exist!`, reconnect it to the graph, and compare all three presentations.

The Litex file uses the builtin `finite_set`, `union`, `cart`, `power_set`,
function carriers, finite enumeration, extensionality, and unique-existence
selection. It does not redeclare those concepts locally.

Run the Litex project from the repository root:

```bash
target/release/litex -strict -r showcases/math_concepts_in_litex/2_sets_functions_and_relations_in_nutshell
```

The handwritten Lean comparison has no imports and uses only Lean 4's Prelude:

```bash
cd lean
lake env lean ../showcases/math_concepts_in_litex/2_sets_functions_and_relations_in_nutshell/same_math_in_lean.lean
```

Because the bare Prelude has no `∃!` notation, the Lean file expands unique
existence into primitive existential and universal propositions, then uses
`Classical.choose`; this makes the comparison with Litex's `have fn ... by
exist!` explicit.

The Litex source contains no trusted steps, but its complete verification is
still blocked by the current migration. The finite-domain membership proof
now uses the proved `first_set $subset N` directly; enumeration of a named
domain is unsupported. Remaining failures are recorded in
[`和showcase有关.md`](../../../plan/迁移的plan/和showcase有关.md).
The Lean comparison was not reverified during this cleanup.

More advanced material—axiomatic set theory, inverse images,
equivalence relations, quotients, cardinal comparison, and
Cantor--Bernstein—is intentionally outside this introductory slice.
