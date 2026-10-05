# Plane Geometry Interfaces

The ambient points are `cart(R, R)`. The standalone source defines 41
objects, functions, and predicates, then proves 186 named theorems.

| Layer | Interfaces |
| --- | --- |
| Coordinate operations | `vec`, `dot`, `det`, `distance_sq` |
| Geometric objects | `line`, `line_through_points`, `circle` |
| Incidence | segments, rays, extensions, affine combinations, collinearity |
| Metric relations | congruent segments and angles, perpendicularity, midpoints |
| Shapes | triangles, parallelograms, rectangles, rhombi, squares |
| Proof consumers | distance and vector formulas, triangle criteria, circle and angle results |

Point domains, nondegeneracy, denominator conditions, and geometric
hypotheses remain as stated in the maintainer's supplied `geo.lit`.
The showcase introduces no additional axioms or trusted proof steps.
