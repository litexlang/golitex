# Mathematical Design: Tarski Geometry from Axioms

## Purpose and scope

This module is a synthetic counterpart to the analytic plane in
`2_euclidean_geometry`. Its authoritative first-version source is the
Schwabhäuser–Szmielew–Tarski axiom hierarchy as exposed by GeoCoq:
dimensionless neutral geometry, decidable point equality, two-dimensionality,
and the Euclidean parallel extension. Continuity, coordinates, angles,
circles, and the hyperbolic extension are deliberately outside the executable
first slice.

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
- **Downstream uses:** Future parallel theorems and a later side-by-side
  hyperbolic extension.
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
- **Downstream uses:** The future midpoint-existence and midpoint-uniqueness
  tracer once the required Chapter 2–7 neutral lemmas exist.
- **Allowable hole:** Existence, uniqueness, and canonical selection are
  intentionally not claimed by the first executable slice.

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
       -> midpoint relation                         [definition]
       -> decidable-equality extension              [source, law]
            -> 2D extension                         [source, law]
                 -> Euclidean extension             [source, law]
                 -> future hyperbolic extension     [source, law]
```

There is no mathematical cycle. The future canonical midpoint selector must
wait for both existence and uniqueness rather than feeding either theorem.

## Intended build order

1. Declare the two primitive relation predicates.
2. Declare the dimensionless neutral setting from the SST/GeoCoq source.
3. Derive segment congruence reflexivity and symmetry.
4. Declare collinearity and midpoint as derived relations and add immediate
   definition-use probes.
5. Layer decidable equality, two-dimensionality, and the Euclidean postulate.
6. In later work, develop neutral betweenness and construction lemmas through
   midpoint uniqueness before adding a canonical midpoint selector.
7. Fix a standard hyperbolic postulate and continuity formulation before
   adding those sibling extensions.

## Interface decisions and permissible gaps

The point-only carrier and the two primitive relation sets are fixed. Settings,
not global axioms or first-class structs, are the public theorem-facing
boundary for this showcase. Midpoint remains a relation until existence and
uniqueness are checked. Euclidean and future hyperbolic theories must share the
neutral prefix rather than copy it. The first slice may omit continuity,
coordinates, and downstream synthetic geometry, but it may not relabel an
unproved or assumed result as checked.
