# Mathematical Collections

## Purpose and scope

This module supplies a small analytic foundation for planar Euclidean geometry.
Points are real coordinate pairs, and geometric relations reduce to checked
set, tuple, and real-arithmetic statements.

## Modeling conventions

Coordinate-consuming signatures use `cart(R, R)`. The exact Cartesian carrier
preserves the projection metadata required for expressions such as `p[1]` and
`p[2]`. The public object `points` remains an alias for that plane.

Squared distance is the primary metric quantity. It avoids unnecessary square
roots in incidence and congruence arguments.

## Important interfaces

### Coordinate plane

- **Meaning:** all real coordinate pairs.
- **Litex form:** `have points set = cart(R, R)`.
- **Dependencies:** `R` and `cart`.
- **Boundary:** coordinate functions still use `cart(R, R)` directly.

### Coordinate operations

- **Meaning:** displacement, dot product, determinant, and squared distance.
- **Litex form:** `have fn vec`, `dot`, `det`, and `distance_sq`.
- **Dependencies:** tuple projections and real arithmetic.
- **Downstream use:** collinearity, line incidence, circles, and congruence.

### Geometric vocabulary

- **Meaning:** lines, circles, collinearity, segment congruence, angle
  congruence, and triangle congruence in the coordinate model.
- **Litex form:** `have fn` for constructed sets and `prop` for relations.
- **Boundary:** these are analytic definitions, not a complete synthetic
  geometry library.

### Metric laws

- **Meaning:** squared distance expands as the sum of two coordinate squares
  and is nonnegative.
- **Litex form:** reusable theorems in `analytic_laws.lit`.
- **Dependencies:** `zero::vec`, `zero::dot`, and real-square
  nonnegativity.

## Dependency map

```text
cart(R, R)
  -> vec, dot, det
  -> distance_sq
  -> lines, circles, and congruence predicates
  -> coordinate formula and distance nonnegativity
```

The current module stops at this foundation.
