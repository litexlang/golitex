# Sets, Functions, and Relations in a Nutshell

This independent showcase is a deliberately small first look at three pieces
of mathematical language that later projects use everywhere:

- two finite sets and concrete membership in their union, intersection, and
  relative difference;
- the successor as a callable function, together with one value and one fact
  about its actual range;
- a binary relation represented directly as a subset of `N x N`; and
- a named theorem proving that successor is injective.

The file uses Litex's builtin `finite_set`, `union`, `intersect`, `set_minus`,
`cart`, `power_set`, `fn_range`, and `$injective`. It does not redeclare any of
those notions locally. The only source-defined mathematical objects are the two
example sets, the successor function, and the one-pair example relation.

Run the Litex project from the repository root:

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/2_sets_functions_and_relations_in_nutshell
```

The handwritten Lean comparison has no imports and uses only Lean 4's Prelude:

```bash
cd lean
lake env lean ../showcases/math_concepts_in_litex/2_sets_functions_and_relations_in_nutshell/same_math_in_lean.lean
```

Both published files are checkable and contain no `trust`, `axiom`, `sorry`,
or `admit`. More advanced material—equivalence relations, quotient sets,
composition of relations, cardinal comparison, and Cantor--Bernstein—is
intentionally outside this introductory slice.
