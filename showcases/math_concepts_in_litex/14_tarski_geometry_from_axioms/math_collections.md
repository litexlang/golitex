# Mathematical Design: Tarski Geometry from Axioms

## Purpose and scope

This module is a synthetic counterpart to the analytic plane in
`2_euclidean_geometry`. Its authoritative source is the
Schwabhäuser–Szmielew–Tarski axiom hierarchy and the Chapter 2–12 definitions
exposed by GeoCoq. The executable target is a source-aligned minimal foundation:
it declares the central relation introduced by each chapter and proves the
neutral dependency chain needed for Euclid I.5, the equality of the base
angles of an isosceles triangle. It also derives GeoCoq's segment-addition and
inner five-segment lemmas, proves SAS and SSS-to-angle for the exact Chapter 11
relation, derives central-reflection existence and uniqueness, and installs
the strict and inclusive Chapter 12 parallel predicates. It does not claim
complete theorem coverage of those GeoCoq
chapters. Continuity, coordinates, circles, and the hyperbolic extension
remain outside this slice.

The intended reader is someone comparing proof interfaces rather than logical
expressive power. The module should show that Litex can keep a point carrier,
two primitive relations, their axioms, and the first derived theorems in one
readable setting-first development.

## Modeling conventions

- `Point` is an arbitrary nonempty carrier; it is not identified with `R^2`.
- Betweenness is a ternary relation represented by a subset of
  `Point × Point × Point`.
- Segment congruence is a quaternary relation represented by a subset of
  `Point × Point × Point × Point`.
- Named settings are theorem-facing assumption bundles. They expose an
  explicit axiom boundary without injecting a global Litex `axiom`.
- Conditional primitive laws are packaged as transparent concrete predicates:
  the full five-segment implication receives a named rule predicate, while
  inner Pasch and the Euclid postulate receive witness-existence result
  predicates. These are
  propositionally the same statements, but give fresh Litex sessions stable
  named proof sources.
- Concrete predicates provide readable judgment interfaces over the primitive
  relation sets.
- A theorem is `checked under the setting`; this does not prove that a model of
  the setting exists.

## Mathematical spine

### Primitive betweenness

- **Ordinary meaning:** `B(A, B, C)` says that `B` lies between `A` and `C`,
  using the non-strict Tarski convention.
- **Semantic role:** Relation.
- **Ideal Litex form:** A first-class ternary relation set plus a concrete
  `prop` wrapper.
- **Interface sketch:** `is_between(Point, Bet, A, B, C)` iff
  `(A, B, C) $in Bet`.
- **Nearest wrong alternative:** A coordinate inequality would silently turn
  the synthetic theory back into the analytic model from showcase 2.
- **Dependencies:** The point carrier supplies the relation signature.
- **Downstream uses:** Pasch, collinearity, midpoint, parallelism.
- **Allowable hole:** No continuity or coordinate characterization is required
  in the first slice.

### Primitive segment congruence

- **Ordinary meaning:** `AB` and `CD` have the same length without introducing
  a numerical length value.
- **Semantic role:** Relation.
- **Ideal Litex form:** A first-class quaternary relation set plus a concrete
  `prop` wrapper.
- **Interface sketch:** `are_segments_congruent(Point, Cong, A, B, C, D)` iff
  `(A, B, C, D) $in Cong`.
- **Nearest wrong alternative:** A `distance` function would import metric or
  real-number structure that Tarski's primitive language intentionally avoids.
- **Dependencies:** The point carrier supplies the relation signature.
- **Downstream uses:** The congruence reflexivity and symmetry tracer, segment
  construction, the five-segment axiom, midpoint.
- **Allowable hole:** A numerical length quotient is not part of this module.

### Dimensionless neutral Tarski setting

- **Ordinary meaning:** The SST neutral core containing pseudo-reflexivity and
  inner transitivity of congruence, congruence identity, segment construction,
  the five-segment axiom, betweenness identity, inner Pasch, and three
  non-collinear witnesses.
- **Semantic role:** Declaration family of assumptions.
- **Ideal Litex form:** `setting TarskiNeutralDimensionlessSetting(...)`.
- **Interface sketch:** The setting carries `Point`, `Bet`, `Cong`, and the
  three lower-dimension witnesses, then states the eight axiom groups directly.
- **Nearest wrong alternative:** A `struct` would make theorem users construct
  and project a stored value even though the first slice only needs a readable
  universal assumption prefix.
- **Dependencies:** Primitive relation sets and equality.
- **Downstream uses:** Every neutral theorem; especially derived congruence
  reflexivity and symmetry.
- **Allowable hole:** Model existence is outside the setting and must remain a
  visible epistemic boundary.

### Two-dimensional and Euclidean extensions

- **Ordinary meaning:** Decidable point equality and the SST upper-dimension
  axiom extend the neutral core to a plane; the SST Euclid axiom then selects
  the Euclidean branch.
- **Semantic role:** Nested declaration families of assumptions.
- **Ideal Litex form:** Three nested settings:
  `TarskiNeutralWithDecidableEqualitySetting`, `Tarski2DSetting`, and
  `TarskiEuclidean2DSetting`.
- **Interface sketch:** Each extension reuses the previous setting bundle and
  states only its new law.
- **Nearest wrong alternative:** Duplicating the complete neutral axiom list in
  each extension would obscure which postulate creates the branch.
- **Dependencies:** Neutral setting, then equality decidability, upper
  dimension, and finally the Euclid axiom.
- **Downstream uses:** Chapter 12 parallel interfaces, the checked Euclid
  witness tracer, and a later side-by-side hyperbolic extension.
- **Allowable hole:** The hyperbolic postulate and continuity layer require a
  separately fixed source formulation before implementation.

### Midpoint

- **Ordinary meaning:** `M` lies between `A` and `B`, and `AM` is congruent to
  `MB`.
- **Semantic role:** Derived relation.
- **Ideal Litex form:** Concrete `prop is_midpoint(...)`.
- **Interface sketch:** `is_between(A, M, B)` together with
  `are_segments_congruent(A, M, M, B)`.
- **Nearest wrong alternative:** A selected `midpoint(A, B)` function would
  claim existence and uniqueness before those theorems have been derived.
- **Dependencies:** Betweenness and segment congruence.
- **Downstream uses:** Perpendicularity and reflection definitions in Chapters
  8–10, plus the checked central-reflection construction interface.
- **Allowable hole:** General midpoint existence is GeoCoq Chapter 8's involved
  orthogonality result, not a Chapter 7 primitive. The I.5 tracer uses a direct
  segment-construction proof and does not smuggle midpoint existence into the
  setting.

### Chapter 2–12 relation layer

- **Ordinary meaning:** The layer follows GeoCoq's source order: congruence
  algebra; betweenness; triangle congruence and collinearity; segment order;
  rays; midpoints; perpendicularity; plane sides and point reflection; line
  reflection; angle congruence; and strict/inclusive parallelism.
- **Semantic role:** Derived relations plus the smallest checked theorem family
  needed to consume them.
- **Ideal Litex form:** Concrete `prop` declarations over `Point`, `Bet`, and
  `Cong`; no coordinate carrier, quotient angle object, or numerical length.
- **Interface sketch:** `are_triangles_congruent`, `is_segment_le`,
  `is_out_on_ray`, `is_perpendicular_at`, `are_on_opposite_sides`,
  `is_line_reflection`, `are_angles_congruent`, `are_strictly_parallel`, and
  `are_parallel` retain the witness-based GeoCoq definitions.
- **Nearest wrong alternative:** Replacing angle congruence by an unexplained
  SSS abbreviation would make Euclid I.5 short but would no longer implement
  GeoCoq Definition 11.2.
- **Dependencies:** Every chapter definition may use only primitive relations
  and earlier chapter interfaces. The Chapter 11 tracer constructs the four
  witnesses in Definition 11.2 directly and uses the five-segment axiom three
  times; this avoids depending on GeoCoq's later Chapter 8 midpoint-existence
  development.
- **Downstream uses:** `isosceles_triangle_has_equal_base_angles`,
  `side_angle_side_gives_third_side`, `triangle_congruence_sas`,
  `triangle_congruence_sss_gives_angles`, reflection laws, and parallel
  incidence projections.
- **Allowable hole:** The public layer need not reproduce every lemma from each
  GeoCoq chapter. Perpendicularity, side, and reflection receive definition-use
  probes but are not artificial dependencies of Euclid I.5.

### Exact side-angle-side theorem

- **Ordinary meaning:** If two pairs of adjacent sides are congruent and their
  included angles are congruent, then the remaining sides are congruent and
  the triangles satisfy Chapter 4's `Cong_3` relation.
- **Semantic role:** Derived theorem family, not an axiom or an alternative
  definition of angle congruence.
- **Ideal Litex form:** A third-side theorem followed by a thin
  `are_triangles_congruent` wrapper.
- **Interface sketch:** `CongA(a,b,c,a2,b2,c2)`, `Cong(a,b,a2,b2)`, and
  `Cong(b,c,b2,c2)` imply `Cong(a,c,a2,c2)` and then `Cong_3`.
- **Nearest wrong alternative:** Defining the angle premise as an SSS fact, or
  silently assuming the desired third-side congruence, would make the theorem
  circular.
- **Dependencies:** Chapter 11's four-witness angle relation, segment
  congruence algebra, segment addition (`l2_11`), and inner five-segment
  (`l4_2`). Decidable point equality handles their degenerate branches.
- **Downstream uses:** A reusable triangle-congruence interface for elementary
  synthetic geometry and later IMO-style proof developments.
- **Allowable hole:** This slice does not yet derive ASA, AAS, RHS, or a
  canonical numerical angle measure.

### Exact SSS-to-angle theorem

- **Ordinary meaning:** Three corresponding side congruences determine the
  corresponding nondegenerate angle in GeoCoq's exact Chapter 11 sense.
- **Semantic role:** Derived theorem, not a replacement definition of angles.
- **Ideal Litex form:** `triangle_congruence_sss_gives_angles` followed by thin
  angle-algebra consumers.
- **Interface sketch:** `Cong_3(a,b,c,a2,b2,c2)`, `a != b`, and `c != b`
  imply `CongA(a,b,c,a2,b2,c2)`.
- **Nearest wrong alternative:** Defining `CongA` as SSS would erase its four
  extension witnesses and make the theorem tautological.
- **Dependencies:** Segment construction, segment addition, two five-segment
  applications, and the exact Chapter 11 relation.
- **Downstream uses:** Angle reflexivity and later SSS-based elementary proofs.
- **Allowable hole:** One-sided angle commutativity, transitivity, and ray
  replacement require the longer Chapter 6/11 transport chain.

### Central reflection construction

- **Ordinary meaning:** Every point has exactly one opposite point through a
  chosen center; reversing the relation returns the starting point.
- **Semantic role:** Existence-and-uniqueness theorem family over the midpoint
  relation.
- **Ideal Litex form:** Relational `point_reflection_exists` and
  `point_reflection_unique`, not an unproved global selector function.
- **Interface sketch:** Segment construction supplies existence;
  `segment_extension_unique` supplies the nondegenerate uniqueness branch.
- **Nearest wrong alternative:** Treating general midpoint existence as a
  primitive axiom would hide GeoCoq Chapter 8's substantial proof.
- **Dependencies:** Five-segment, congruence identity, and decidable point
  equality only for the degenerate/nondegenerate uniqueness split.
- **Downstream uses:** Reflection, midpoint, and later perpendicular arguments.
- **Allowable hole:** General midpoint existence and uniqueness for arbitrary
  endpoints remain separate later theorems.

### Strict and inclusive parallelism

- **Ordinary meaning:** `Par_strict` means two nondegenerate coplanar lines
  have no common point; GeoCoq's inclusive `Par` also permits coincident
  nondegenerate lines.
- **Semantic role:** Chapter 12 relation layer plus definition-use projections.
- **Ideal Litex form:** Separate concrete predicates
  `are_strictly_parallel` and `are_parallel`.
- **Interface sketch:** A named common-point existential makes the strict
  no-intersection clause atomic; the inclusive predicate is a disjunction with
  the named coincident-line branch.
- **Nearest wrong alternative:** Using one ambiguous word `parallel` without
  saying whether coincident lines count would make later theorems unstable.
- **Dependencies:** Collinearity and coplanarity definitions only. The SST
  Euclid law enters separately through `euclid_postulate_supplies_intersections`.
- **Downstream uses:** Later Playfair, alternate-angle, and transversal results.
- **Allowable hole:** Parallel existence, uniqueness, and transitivity are not
  yet derived in this checkpoint.

## Dependency map

Edge legend: `signature` supplies a carrier to a relation; `law` introduces a
setting assumption; `definition` unfolds a derived predicate; `proof` is a
checked theorem dependency; `source` is an explicit axiom boundary.

```text
Point
  -> Bet, Cong                                      [signature]
  -> neutral SST setting                            [source, law]
       -> congruence reflexivity                    [proof]
       -> congruence symmetry                       [proof]
       -> congruence algebra (Ch2)                  [proof]
       -> betweenness algebra (Ch3)                 [proof]
            -> Cong_3 and Col (Ch4)                 [definition]
            -> segment order (Ch5)                  [definition]
            -> rays (Ch6)                           [definition]
            -> midpoint relation (Ch7)              [definition]
            -> perpendicularity (Ch8)               [definition]
            -> plane sides and point reflection (Ch9) [definition]
            -> line reflection (Ch10)               [definition]
            -> exact angle congruence (Ch11)         [definition, proof]
                 -> isosceles base angles            [proof]
                 -> SSS-to-angle and angle algebra   [proof]
            -> central reflection construction       [proof]
            -> strict/inclusive parallelism (Ch12)   [definition, proof]
       -> decidable-equality extension              [source, law]
            -> segment addition (l2_11)              [proof]
            -> inner five-segment (l4_2)             [proof]
            -> exact SAS third side                  [proof]
                 -> triangle congruence (Cong_3)     [definition, proof]
            -> 2D extension                         [source, law]
                 -> Euclidean extension             [source, law]
                      -> Euclid witness tracer       [proof]
                 -> future hyperbolic extension     [source, law]
```

There is no mathematical cycle. The future canonical midpoint selector must
wait for both existence and uniqueness rather than feeding either theorem.

## Intended build order

1. Declare the two primitive relation predicates.
2. Declare the dimensionless neutral setting from the SST/GeoCoq source.
3. Derive segment congruence reflexivity and symmetry.
4. Add the Chapter 2–4 congruence, betweenness, triangle-congruence, and
   collinearity foundation.
5. Add the Chapter 5–7 segment-order, ray, and midpoint relation layer.
6. Add the Chapter 8–10 perpendicularity, side, and reflection definitions
   with use probes.
7. Add exact GeoCoq-style angle congruence and prove Euclid I.5 by direct
   construction of its four witnesses plus three five-segment applications.
8. Layer decidable equality; derive segment addition and inner five-segment,
   then prove the exact Chapter 11 SAS third-side and `Cong_3` theorems.
9. Add SSS-to-angle, angle algebra, fixed-ray construction uniqueness, and the
   central-reflection existence-and-uniqueness interface.
10. Add two-dimensionality, the Euclidean postulate, and exact Chapter 12
   strict/inclusive parallel definitions; verify the Euclid tracer fails when
   its setting is weakened to the plane layer.
11. Fix a standard hyperbolic postulate and continuity formulation before
   adding those sibling extensions.

## Interface decisions and permissible gaps

The point-only carrier and the two primitive relation sets are fixed. Settings,
not global axioms or first-class structs, are the public theorem-facing
boundary for this showcase. Midpoint remains a relation; this slice does not
claim GeoCoq Chapter 8's later general existence theorem. Angle congruence
uses GeoCoq Definition 11.2 rather than a
numerical angle or an SSS alias. Euclid I.5 must typecheck under the neutral
setting, demonstrating that the Euclidean parallel axiom is unrelated to this
theorem. SAS uses the neutral-with-decidable-equality setting because the
source-aligned segment-addition and inner-five proofs split degenerate point
equalities; it does not consume upper dimension or Euclid. The slice may omit
general midpoint existence, angle transitivity and ray replacement,
vertical/supplementary angles, ASA/AAS/RHS, Playfair-style parallel theorems,
continuity, coordinates, and unrelated downstream theorems, but it may not
relabel an unproved or assumed result as checked.
