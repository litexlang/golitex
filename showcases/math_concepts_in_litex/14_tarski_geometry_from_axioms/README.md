# Tarski Geometry from Axioms

This independent showcase is the synthetic counterpart to
`2_euclidean_geometry`. Instead of choosing coordinates in `R^2`, it starts
with one point carrier and two primitive relations: ternary betweenness and
quaternary segment congruence.

The executable Litex slice contains:

- the Schwabhäuser–Szmielew–Tarski dimensionless neutral axiom bundle;
- nested extensions for decidable point equality, two-dimensionality, and the
  Euclidean parallel postulate;
- checked derivations of ordinary segment-congruence reflexivity and symmetry;
  and
- relational definitions of collinearity and midpoint.

Run it from the repository root with:

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/14_tarski_geometry_from_axioms
```

The public Litex file has no `trust`, global `axiom`, or `abstract_prop`.
Its axiomatic boundary is visible in named `setting` declarations: the derived
theorems are checked under those assumptions, but this showcase does not claim
to construct a model of them. Midpoint deliberately remains a relation; its
existence and uniqueness require a much longer neutral-geometry development.
Continuity, coordinates, angles, circles, and an executable hyperbolic sibling
are outside this first slice.

The axiom hierarchy and tracer proof follow the public
[GeoCoq Tarski interfaces](https://geocoq.github.io/GeoCoq/html/GeoCoq.Axioms.tarski_axioms.html).
The early congruence lemmas are shown in
[GeoCoq Chapter 2](https://geocoq.github.io/GeoCoq/html/GeoCoq.Tarski_dev.Ch02_cong.html),
while midpoint theory appears much later in
[GeoCoq Chapter 7](https://geocoq.github.io/GeoCoq/html/GeoCoq.Tarski_dev.Ch07_midpoint.html).

`same_math_in_lean.lean` gives a no-import, handwritten Lean analogy. It uses
explicit structures for the same assumption bundles and proves the same first
three results without `axiom`, `sorry`, or `admit`. Run it with:

```bash
lean showcases/math_concepts_in_litex/14_tarski_geometry_from_axioms/same_math_in_lean.lean
```
