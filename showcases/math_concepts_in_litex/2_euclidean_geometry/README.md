# Euclidean Geometry

This independent first version fixes an analytic plane over `R^2` and checks:

- displacement, dot product, squared distance, and the `3-4-5` computation;
- segment congruence and the equilateral-triangle relation;
- an explicit counterclockwise equilateral vertex;
- the sixty-degree rotation norm identity and both endpoint-distance laws;
  and
- Euclid Book I, Proposition 1, consumed on the base `(0,0)` to `(2,0)` with
  apex `(1, sqrt(3))`.

Run it from the repository root with:

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/2_euclidean_geometry
```

The module has no `trust` or local axiom. Its analytic model is intentional and
narrower than a synthetic Euclidean axiom system; the result does not claim to
formalize all of Euclid's foundations.

`same_math_in_lean.lean` uses Prelude integers for the exact
coordinate and `3-4-5` calculations. The square-root-dependent equilateral
vertex lemma is exposed as a named setting boundary, then consumed to construct
the Euclid I.1 witness. It has no imports and is a handwritten formulation of the same mathematics, not
compiler-generated output. Run it with:

```sh
lean showcases/math_concepts_in_litex/2_euclidean_geometry/same_math_in_lean.lean
```
