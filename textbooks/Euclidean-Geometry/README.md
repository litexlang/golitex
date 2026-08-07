# Euclidean Geometry

> **Development status:** This module is developed in public and may contain
> work at different maturity levels. Its presence in the repository is not a
> completion claim; the verification evidence, explicit `trust` boundaries,
> and known limitations below describe what is currently established.

This module is the first analytic-model implementation of elementary
Euclidean geometry in Litex. Points are coordinate pairs in `cart(R, R)`, and
geometric objects are defined as concrete sets and functions over that plane.

## One checked tracer: Euclid I.1

A domain language matters only if later mathematics can state and use geometry
as geometry. The tracer for this module is Euclid I.1: given two distinct
points, construct a third point that makes an equilateral triangle. Its public
theorem is written in geometric vocabulary:

<!-- litex:skip-test -->

```litex
thm euclid_book1_proposition_1:
    ? forall a, b cart(R, R):
        a != b
        =>:
            exist c cart(R, R) st {$zero::is_equilateral_triangle(a, b, c)}
    zero::distance_sq(a, equilateral_vertex(a, b)) = zero::distance_sq(a, b)
    zero::distance_sq(b, equilateral_vertex(a, b)) = zero::distance_sq(a, b)
    $zero::are_segments_congruent(a, b, a, equilateral_vertex(a, b))
    $zero::are_segments_congruent(a, b, b, equilateral_vertex(a, b))
    $zero::is_equilateral_triangle(a, b, equilateral_vertex(a, b))
    witness exist c cart(R, R) st {$zero::is_equilateral_triangle(a, b, c)} from equilateral_vertex(a, b)
```

This is an excerpt from the registered theorem in `book01_01_04.lit`, not a
separate standalone demo. The reader-facing proof says which two segment
congruences establish the equilateral triangle and names the constructed
witness. The coordinate expansion is isolated in
`equilateral_vertex_distance_lemma`, which is checked in the same module. This
separation is the point of the experiment: machine-oriented algebra remains
auditable without becoming the language in which every later geometric
argument must be read.

## Why the Lean and AlphaGeometry comparison is central

The relevant claim is not that Lean has no Euclidean geometry. Mathlib already
contains substantial general infrastructure, including
[Euclidean triangle theorems](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Euclidean/Triangle.html)
and
[two-dimensional circle-intersection facts](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Euclidean/Basic.html).
The practical gap for olympiad geometry lies between that general analytic and
affine foundation and a ready-to-use language organized around incidence,
collinearity, perpendicularity, cyclicity, similarity, angle chasing, and
auxiliary constructions.

Google DeepMind's 2024 IMO system makes this distinction concrete. AlphaProof
handled general formal reasoning, while the geometry problem was handled by
the specialized AlphaGeometry 2 system
([official report](https://deepmind.google/blog/ai-solves-imo-problems-at-silver-medal-level/)).
The released AlphaGeometry implementation has explicit point, line, and circle
objects together with separate construction definitions and deduction rules
([source repository](https://github.com/google-deepmind/alphageometry)). Its
success is evidence that domain organization is not cosmetic: it changes the
representation, proof search, and readable proof steps available to the
solver.

The three systems therefore illuminate different layers rather than forming a
simple winner-versus-loser comparison:

| Layer | What it contributes | Relevant boundary |
| --- | --- | --- |
| Lean and mathlib | A mature general prover and broad analytic/affine Euclidean foundations | An olympiad-facing synthetic interface still has to be selected and organized for the task |
| AlphaGeometry | A geometry-specific representation, construction language, and symbolic deduction engine | It is a specialized geometry prover rather than a general checked-mathematics authoring language |
| This Litex module | Geometry vocabulary written as ordinary Litex definitions and theorems, backed here by a coordinate model | The current slice covers only Euclid I.1--I.4 and is not yet an olympiad geometry engine |

This comparison is important because it locates a stronger purpose for Litex
than merely shortening tactic scripts. Mature general foundations do not by
themselves determine the language in which a field should be practiced. At the
other extreme, a successful domain prover may build a separate language and
engine for that one field. Litex tests a middle hypothesis:

> A mathematical domain language can itself be readable, reusable, checked
> mathematics: domain concepts form the public proof interface, while a small
> general kernel checks their definitions, implementations, and consequences.

In the I.1 tracer, `is_equilateral_triangle` is that public interface;
`equilateral_vertex_distance_lemma` is its analytic implementation; and the
final existential witness is the checked geometric result. No
geometry-specific kernel rule is added for this slice. Sets, Cartesian pairs,
real arithmetic, and square-root facts carry the implementation. If this
pattern scales, AI may generate coordinate or algebraic detail while the
durable theorem and proof remain reviewable in the vocabulary of geometry.

## What this module does not yet establish

This first slice is evidence for a direction, not evidence that Litex already
solves olympiad geometry. It currently uses an analytic coordinate model and
checks only Euclid I.1--I.4. It does not yet provide a complete synthetic layer
for general intersections, directed angles, cyclic quadrilaterals, similar
triangles, power of a point, transformations, or auxiliary-construction
search. Litex's trusted base and review maturity also must not be presented as
equivalent to Lean's.

The decisive next benchmark is therefore a construction-heavy olympiad
geometry slice. A successful result should keep the final problem and proof
mostly in geometric relations, discharge the implementation through the
analytic layer, add no problem-specific kernel rules, expose every remaining
`trust`, and report verification time and proof-interface size. That would
test whether the I.1 separation survives real geometry rather than merely
whether coordinate algebra can prove four early propositions.

The registered project contains three source files:

- `book_zero.lit` for the coordinate plane and foundational vocabulary;
- `analytic_laws.lit` for checked coordinate and metric laws;
- `book01_01_04.lit` for Euclid's Book I, Propositions 1--4.

`book_zero.lit` exposes `points`, `vec`, `dot`, `det`, `distance_sq`, `line`,
`is_line`, `lines`, `circle`, collinearity, and congruence predicates. It also
contains checked probes for carrier transport, the 3-4-5 distance, and line
incidence.

`analytic_laws.lit` proves the coordinate formula and nonnegativity of squared
distance. `book01_01_04.lit` exposes explicit coordinate witnesses and named
theorems `euclid_book1_proposition_1` through
`euclid_book1_proposition_4`. All four propositions and their analytic support
lemmas are checked without local `trust`: the equilateral apex uses a
rotation-norm identity, the cut point uses square-root ratio bounds and affine
distance scaling, and SAS uses the dot-determinant norm identity plus a
coordinate law of cosines.

Verified with:

```text
target/release/litex -compact -runner -f scripts/Euclidean_Geometry/textbook/book_zero.lit
target/release/litex -compact -runner -f scripts/Euclidean_Geometry/textbook/analytic_laws.lit
target/release/litex -compact -runner -f scripts/Euclidean_Geometry/textbook/book01_01_04.lit
target/release/litex -compact -runner -r scripts/Euclidean_Geometry/textbook
```

Translation notes, todos, experiments, and proof journals live in the paired
workspace `scripts/Euclidean_Geometry/`; they are not part of this module.
