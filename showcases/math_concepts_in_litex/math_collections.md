# Collection-Level Mathematical Design

The collection is a numbered reader sequence, not a monolithic library. Every
module is independently executable and owns a single main line with a few
classic examples.

## Reader sequence

```text
1 middle-school mathematics
  -> 2 Euclidean geometry
  -> 3 number theory
  -> 4 discrete mathematics
  -> 5 linear algebra
  -> 6 abstract algebra
  -> 7 single-variable calculus
  -> 8 probability and statistics
  -> 9 topology
  -> 10 real analysis
  -> 11 multivariable calculus
  -> 12 ordinary differential equations
  -> 13 numerical analysis
  -> 14 Tarski geometry from axioms
```

The arrows mean suggested reading order only. Shared interfaces should move to
`std` only after at least two real consumers need the same stable shape.

## Cross-cutting interface choices

- Reuse native number systems, sets, tuples, finite sequences, arithmetic,
  `gcd`, `finite_set_size`, and other Builtins.
- Prefer relations and named settings for theorem-facing assumptions.
- Use a struct only when a mathematical structure must be a first-class value.
- Keep existence relational until uniqueness justifies a selector.
- Make every denominator, domain restriction, and trust boundary visible.
- Put proof iteration under `.drafts/proof_journals/`, never beside published
  artifacts.

## Shared non-goals

These showcases are not a complete undergraduate curriculum, a replacement
for textbooks, or a claim that Prelude-only Lean is representative of Mathlib.
They are small checked examples of how the same mathematics can be presented
through Litex's setting-first interface and through explicit Lean structures.
