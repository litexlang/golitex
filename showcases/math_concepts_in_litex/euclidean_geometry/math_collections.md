# Mathematical Design: Euclidean Geometry

## Implemented first-version slice

`main.lit` now checks the analytic plane, squared distance, segment congruence,
the explicit oriented equilateral vertex, its rotation-norm and distance
lemmas, and Euclid I.1. The concrete `(0,0)`--`(2,0)` base evaluates to apex
`(1,sqrt(3))`. The file contains no direct `trust`.

## Core interface cards

### Point and displacement

- **Meaning:** points live in `R^2`; `vec(A,B)` is the displacement `B-A`.
- **Form:** carrier alias as `have`, displacement as `have fn`.
- **Rejected form:** an abstract `Point` carrier with trusted coordinate laws;
  that would pretend a synthetic foundation while all proofs use coordinates.
- **Use:** every metric and incidence relation.

### Squared distance

- **Meaning:** dot product of displacement with itself.
- **Form:** `have fn` returning `R`.
- **Rejected form:** only a congruence relation; callers need the value for
  calculations and constructions.
- **Use:** congruence, circles, equilateral vertex.

### Collinearity and perpendicularity

- **Meaning:** determinant zero and dot product zero, respectively.
- **Form:** `prop` relations on supplied points/vectors.
- **Rejected form:** Boolean functions or structures; they classify supplied
  data and no caller projects fields.

### Line and circle

- **Meaning:** loci satisfying affine or fixed-distance equations.
- **Form:** set-valued `have fn` with explicit nondegeneracy/positive-radius
  constraints; optional `is_line` relation for proposed sets.
- **Rejected form:** only incidence predicates, because later callers need
  intersections and set membership.

### Equilateral vertex

- **Meaning:** the selected counterclockwise apex constructed on directed base
  `a -> b`.
- **Form:** formula-defined `have fn`; no unique-existence selection is needed
  because orientation chooses an explicit formula.
- **Rejected form:** only `exist c` without a callable construction, or an
  unqualified unique apex (there are two without orientation).
- **Use:** witness for Euclid I.1.

## Main dependency DAG

```text
R and R^2
  -> vec                                         [signature, definition]
  -> dot, det                                    [definition]
  -> distance_sq, collinear                      [definition]
  -> segment congruence, circle                  [definition]
  -> equilateral-triangle relation               [definition]

sqrt(3) and coordinate algebra
  -> rotation norm identity                      [proof]
  -> equilateral_vertex                          [definition]
  -> endpoint distance equalities                [proof]
  -> Euclid I.1                                  [existence, proof]
```

The principal source/trust boundary is the Builtin real-number and square-root
foundation. It must be disclosed, but this project should not reprove real
analysis. No additional local axiom should be introduced for the flagship.
