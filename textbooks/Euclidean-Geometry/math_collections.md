# Mathematical Collections

## Purpose and scope

This module constructs an analytic model of elementary Euclidean plane
geometry over `R`. Its first source-facing target is Euclid's *Elements*, Book
I, Propositions 1--4. The intended downstream users are later Book I
propositions and coordinate proofs of olympiad geometry. Three-dimensional
geometry, area theory, and the full parallel-postulate development are outside
the first version.

## Modeling conventions

Points and coordinate vectors use the carrier `cart(R, R)`. A line is an
element of `power_set(cart(R, R))` satisfying one nondegenerate affine linear
equation; the set of all lines is therefore a subset of that power set. Point
incidence uses native membership `P $in L`.

Geometric equality is not coefficient equality. Scaled triples `(a,b,c)` and
`(k*a,k*b,k*c)` may present the same line. Public line identity is set
extensionality. Squared distance is primary so that early incidence and
congruence arguments avoid unnecessary square roots.

Euclid's incidence and metric commitments are interpreted inside a concrete
model rather than introduced as primitive geometric axioms. The actual base
assumptions are Litex's set theory, the real-number ordered-field surface, and
square-root facts. Euclid's numbered propositions are source-facing theorems
in that model. The I.1--I.4 slice now has no local trust boundary; future
proof gaps must remain narrow and visible rather than replacing a geometric
definition.

The public `points` alias is useful as mathematical vocabulary, but the first
implementation found that it does not preserve the Cartesian projection
metadata needed while checking function bodies. Coordinate-consuming
signatures therefore use the exact carrier `cart(R, R)`; membership can be
transported to `points` after exact Cartesian membership is established.

## Euclid's axioms and this analytic model

Euclid's five common notions are the equality rules (things equal to the same
thing are equal; adding or subtracting equals preserves equality; coincident
things are equal; the whole is greater than the part). In this module they are
not restated as geometric axioms: equality, substitution, arithmetic, and
order are inherited from Litex and `R`.

The five geometric postulates are: draw a straight line between two points;
extend a finite straight line; draw a circle from a center and radius; all
right angles are equal; and the parallel postulate. In the present model:

- line and circle objects are already concrete sets of points;
- I.1 uses an explicit equilateral apex instead of assuming a general
  circle-circle intersection theorem;
- I.2 uses coordinate translation instead of Euclid's I.1/P1/P2/P3 chain;
- I.3 uses an affine cut point instead of Euclid's I.2/P2/P3 chain;
- I.4 replaces superposition with a coordinate SAS third-side lemma;
- named line-through-two-points, segment-extension, right-angle, and parallel
  postulate theorems remain work for the next layer.

Thus this is a model-theoretic first version: its geometric claims reduce to
set membership and real algebra. It does not claim that all five postulates
have already been exposed as checked public theorems.

## Mathematical spine

### Coordinate plane

- **Ordinary meaning:** The real Cartesian plane containing every point used by the module.
- **Semantic role:** Carrier object.
- **Ideal Litex form:** `have`.
- **Interface sketch:** `have points set = cart(R, R)`.
- **Nearest wrong alternative:** An abstract `Point` predicate would discard the concrete coordinate model.
- **Dependencies:** `R` and `cart` by definition.
- **Downstream uses:** All point-valued functions and relations. Probe: `(0, 0) $in points`.
- **Allowable hole:** None in the intended interface.

### Coordinate vector operations

- **Ordinary meaning:** Displacement, dot product, determinant, and squared norm in the plane.
- **Semantic role:** Formula-defined functions.
- **Ideal Litex form:** `have fn`.
- **Interface sketch:** `vec(A,B)`, `dot(u,v)`, `det(u,v)`, and `distance_sq(A,B)`.
- **Nearest wrong alternative:** Relations carrying proposed outputs would make ordinary algebra unusably indirect.
- **Dependencies:** Coordinate projection and real arithmetic by definition.
- **Downstream uses:** Collinearity, perpendicularity, congruence, circles, and triangle proofs.
- **Allowable hole:** Algebraic identities may require small explicit verifier bridges.

### Analytic metric laws

- **Ordinary meaning:** Coordinate expansion, nonnegativity, symmetry, and scaling laws for squared Euclidean distance.
- **Semantic role:** Reusable named mathematical results between the raw coordinate definitions and Book I constructions.
- **Ideal Litex form:** reusable `thm` declarations in `analytic_laws.lit`, plus source-local bridge theorems when they depend on a Book I construction.
- **Interface sketch:** `distance_sq_coordinate_formula`, `distance_sq_nonnegative`, distance symmetry and positivity, affine squared-distance scaling, the dot-determinant norm identity, and the coordinate law of cosines.
- **Nearest wrong alternative:** Repeating opaque local algebra makes every later circle, cutoff, and congruence proof harder to inspect and reuse.
- **Dependencies:** `zero::vec`, `zero::dot`, `zero::distance_sq`, real arithmetic, and square nonnegativity.
- **Downstream uses:** Equilateral construction, cut-point construction, circle facts, and coordinate SAS.
- **Allowable hole:** None for the laws used by I.1--I.4. Later angle arithmetic and circle-intersection laws must remain separately visible until proved.

### Lines as point sets

- **Ordinary meaning:** The locus `a*x + b*y + c = 0` for coefficients with `a` and `b` not both zero.
- **Semantic role:** Set-valued construction plus a classification relation.
- **Ideal Litex form:** `line` as `have fn`, `is_line` as `prop`, and `lines` as `have`.
- **Interface sketch:** `line(a,b,c)`, `$is_line(L)`, and `L $in lines`.
- **Nearest wrong alternative:** A coefficient struct gives different objects for scaled presentations of one geometric line.
- **Dependencies:** Coordinate plane by signature and real arithmetic by definition.
- **Downstream uses:** Native incidence, collinearity, intersections, and Euclid's first postulate.
- **Allowable hole:** Direct membership in the set-builder `lines` must be verified in the registered module context.

### Segment congruence and circles

- **Ordinary meaning:** Two segments are congruent when their squared lengths agree; a circle is the locus of points at a fixed squared distance from its center.
- **Semantic role:** Relation and set-valued construction.
- **Ideal Litex form:** `are_segments_congruent` as `prop`; `circle` as `have fn`.
- **Interface sketch:** `$are_segments_congruent(A,B,C,D)` and `circle(O,r)`.
- **Nearest wrong alternative:** Taking a numerical angle or distance as primitive adds selection and square-root obligations before they are needed.
- **Dependencies:** Squared distance by definition.
- **Downstream uses:** Euclid I.1--I.4 and later metric geometry.
- **Allowable hole:** General circle-intersection existence is beyond the first version; I.1 may use an explicit coordinate witness.

### Euclid I.1--I.4

- **Ordinary meaning:** Equilateral-triangle construction, segment transport, segment cutoff, and SAS congruence.
- **Semantic role:** Source-facing mathematical results.
- **Ideal Litex form:** Named `thm` declarations in source order.
- **Interface sketch:** Existential conclusions for I.1--I.3 and a congruence conclusion for I.4.
- **Nearest wrong alternative:** Encoding each result as an abstract proposition would hide the construction and the omitted Euclidean dependencies.
- **Dependencies:** Coordinate operations, congruence, betweenness where applicable, and real algebra by proof.
- **Downstream uses:** Euclid I.5 onward and reusable olympiad geometry constructions.
- **Current proof boundary:** I.1--I.4 and all analytic support lemmas are checked without local `trust`. The next boundary is new geometry for I.5 onward, not unfinished debt inside these four propositions.

## Dependency map

Edge legend: `--definition-->` unfolds a definition; `--signature-->` supplies
a carrier; and `--proof-->` is a mathematical proof dependency.

```text
R and cart
  --definition--> points
points
  --signature--> vec, dot, det, distance_sq
vec and det
  --definition--> collinear and line_through
distance_sq
  --proof--> analytic metric laws
analytic metric laws
  --definition/proof--> segment congruence and circle
line, circle, segment congruence
  --proof--> Euclid I.1--I.3
distance_sq and angle congruence
  --proof--> Euclid I.4 (checked Gram identity, scale cancellation, and law of cosines)
Euclid I.1--I.4
  --proof--> later Book I propositions
```

## Intended build order

1. Register the coordinate carrier and vector operations.
2. Add line, circle, collinearity, congruence, and representative use probes.
3. Prove Euclid I.1 by an explicit coordinate construction.
4. Add source-facing I.2 and I.3 with the smallest natural coordinate constructions available.
5. Define the angle/congruence surface needed by I.4 and attempt SAS directly.
6. Preserve the solved proof patterns and liveness evidence, then extend toward I.5--I.15.

This order deliberately inserts the analytic `Book Zero` that Euclid used
implicitly. The numbered propositions remain in Euclid's source order.

## Interface decisions and permissible gaps

The point carrier, set-valued line representation, native incidence, and
squared-distance congruence are stable decisions. A coefficient record must
not replace line sets, and a candidate relation must not replace a function
that later code needs to apply. General betweenness, same-side relations,
circle intersections, rigid motions, and full angle arithmetic may remain
designed but unimplemented after this first slice. Any future proof gap must
name the exact missing result and its downstream consumers in the paired
workspace.
