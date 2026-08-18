# Tarski Geometry from Axioms

This independent showcase is the synthetic counterpart to
`2_euclidean_geometry`. Instead of choosing coordinates in `R^2`, it starts
with one point carrier and two primitive relations: ternary betweenness and
quaternary segment congruence.

The executable Litex slice now contains:

- the Schwabhäuser–Szmielew–Tarski dimensionless neutral axiom bundle;
- nested extensions for decidable point equality, two-dimensionality, and the
  Euclidean parallel postulate;
- a source-ordered Chapters 2–12 relation layer: congruence algebra,
  betweenness, collinearity, segment order, rays, midpoint, perpendicularity,
  sides, point/line reflection, coplanarity, and exact angle congruence;
- a checked neutral proof of Euclid I.5: an isosceles triangle has equal base
  angles; and
- GeoCoq-aligned segment addition and inner five-segment lemmas, followed by
  exact side-angle-side: two congruent adjacent sides and congruent included
  angles imply the third side, hence triangle congruence;
- the converse SSS-to-angle bridge for the exact four-witness Chapter 11
  relation, plus reflexive, symmetric, and simultaneous-arm-reversal laws;
- triangle-congruence equivalence laws, same-ray algebra, segment-extension
  uniqueness, and central-reflection existence, uniqueness, fixed-center, and
  involution laws; and
- GeoCoq Chapter 12 `Par_strict` and inclusive `Par`, their first projection
  theorems, and a checked tracer for the SST Euclid intersection witnesses.

Run it from the repository root with:

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/14_tarski_geometry_from_axioms
```

The public Litex file has no `trust`, global `axiom`, or `abstract_prop`. Its
axiomatic boundary is visible in named `setting` declarations: the derived
theorems are checked under those assumptions, but this showcase does not claim
to construct a model of them. Midpoint deliberately remains a relation;
GeoCoq's general midpoint-existence proof is a later and much longer
orthogonality development. The I.5 proof instead constructs the four witnesses
required by angle congruence directly, then uses the five-segment axiom three
times. Thus I.5 needs neither the upper-dimension axiom nor Euclid's parallel
postulate. The SAS proof unfolds the witness-based Chapter 11 angle relation,
aligns its four extension witnesses using segment addition, and applies the
inner five-segment theorem twice. Its source-aligned proof uses decidable point
equality to separate degenerate cases, but still needs neither the
upper-dimension axiom nor Euclid's parallel postulate.

The Euclidean tracer has a negative dependency probe: the identical
intersection conclusion fails under `Tarski2DSetting` and verifies only under
`TarskiEuclidean2DSetting`. Thus the file distinguishes definition-level
parallelism, neutral incidence theorems, the upper-dimension plane law, and
the genuinely Euclidean postulate. General midpoint existence, angle
transitivity and ray replacement, vertical/supplementary angle theorems,
ASA/AAS/RHS, and Playfair-style parallel existence/uniqueness remain later
proof layers rather than hidden assumptions.

The axiom hierarchy follows the public
[GeoCoq Tarski interfaces](https://geocoq.github.io/GeoCoq/html/GeoCoq.Axioms.tarski_axioms.html).
The chapter layer tracks the public
[GeoCoq definitions](https://geocoq.github.io/GeoCoq/html/GeoCoq.Tarski_dev.Definitions.html)
and Chapters
[2](https://geocoq.github.io/GeoCoq/html/GeoCoq.Tarski_dev.Ch02_cong.html),
[3](https://geocoq.github.io/GeoCoq/html/GeoCoq.Tarski_dev.Ch03_bet.html),
[4a](https://geocoq.github.io/GeoCoq/html/GeoCoq.Tarski_dev.Ch04_col.html),
[4b](https://geocoq.github.io/GeoCoq/html/GeoCoq.Tarski_dev.Ch04_cong_bet.html),
[7](https://geocoq.github.io/GeoCoq/html/GeoCoq.Tarski_dev.Ch07_midpoint.html),
[8](https://geocoq.github.io/GeoCoq/html/GeoCoq.Tarski_dev.Ch08_orthogonality.html),
[11](https://geocoq.github.io/GeoCoq/html/GeoCoq.Tarski_dev.Ch11_angles.html),
and [12](https://geocoq.github.io/GeoCoq/html/GeoCoq.Tarski_dev.Ch12_parallel.html).
This is a minimal usable interface and theorem spine, not a claim of theorem
parity with all ten GeoCoq chapters.

`same_math_in_lean.lean` gives a no-import, handwritten Lean analogy. It uses
explicit structures for the same assumption bundles, defines the same Chapters
2–12 relations, and independently proves I.5, exact SAS, SSS-to-angle, the
reflection and parallel interfaces, and the same algebraic theorem families
without `axiom`, `sorry`, or `admit`. Run it with:

```bash
cd lean
lake env lean ../showcases/math_concepts_in_litex/14_tarski_geometry_from_axioms/same_math_in_lean.lean
```
