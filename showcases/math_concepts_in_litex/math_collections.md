# Collection-Level Mathematical Design

The collection is a numbered reader sequence, not a monolithic library. Every
module is independently executable and owns a single main line with a few
classic examples.

## Reader sequence

```text
1 middle-school mathematics
  -> 2 sets, functions, and relations
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
  -> 15 generic small categories plus two finite instances encoded inside set theory
  -> 16 probability theory from the Kolmogorov axioms
```

The arrows mean suggested reading order only. Shared interfaces should move to
`std` only after at least two real consumers need the same stable shape.

## Completion contract and stop lines

“Complete” in this collection means a vertical slice, not a survey course:
setting or structure, morphism or subobject, construction, consuming theorem,
and concrete instance. Once those five layers are checked, adding adjacent
chapters is optional rather than necessary cleanup.

| Direction | First-version stopping line |
| --- | --- |
| linear algebra | kernels and zero-kernel iff injective; no bases, dimension, rank-nullity, or quotients |
| abstract algebra | normal group kernels; ring kernels; prime ideal iff supplied quotient presentation is a domain; no maximal-ideal correspondence, modules, or extension theory |
| topology | closed-preimage continuity and compact images; no filters, separation hierarchy, or connectedness |
| calculus / real analysis | grow at most through Rolle/MVT and elementary consequences; integration/FTC are a later independent slice |
| multivariable / differential geometry | Euclidean total derivatives, Jacobians, gradients, and elementary curves only; no manifold machinery |
| ODE | explicit checked IVPs; Picard--Lindelof optional, with systems/stability/BVPs outside the first version |
| numerical analysis | one exact iterative method, a quantitative residual bound, and a checked executable step; no floating-point roundoff proof |
| category theory | categories, functors, natural transformations, identity/composition, terminal consumer; no limits, adjunctions, Yoneda, monads, or general functor categories |
| functional analysis (future) | normed and Banach spaces, bounded linear maps, Banach fixed point |
| PDE (future) | a few explicit classical solutions only; no weak/Sobolev/general existence theory |

Algebraic geometry, homological algebra, representation theory, model theory,
and universal algebra are not planned collection directions. A future row does
not justify an empty project: create a directory only when its first checked
vertical slice exists.

## Cross-cutting interface choices

- Reuse native number systems, sets, tuples, finite sequences, arithmetic,
  `gcd`, `finite_set_size`, and other Builtins.
- Prefer relations and named settings for theorem-facing assumptions.
- Use a struct only when a mathematical structure must be a first-class value.
- Keep existence relational until uniqueness justifies a selector.
- Use dependent function carriers when a selected value must land in a set
  determined by earlier arguments, as in category identities and composition.
- Make every denominator, domain restriction, and trust boundary visible.
- Put proof iteration under `.drafts/proof_journals/`, never beside published
  artifacts.

## Shared non-goals

These showcases are not a complete undergraduate curriculum, a replacement
for textbooks, or a claim that Prelude-only Lean is representative of Mathlib.
They are small checked examples of how the same mathematics can be presented
through Litex's setting-first interface and through explicit Lean structures.
