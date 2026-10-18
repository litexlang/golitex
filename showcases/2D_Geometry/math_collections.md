# Geometry interfaces

## Purpose and scope

This library models Euclidean plane geometry with real coordinate pairs.
`geo_definitions.lit` provides the vocabulary; `geo.lit` repeats that vocabulary
and supplies theorems. Keep their definition prefixes identical. The IMO
packages are independent developments with local definitions.

## Modeling conventions and mathematical spine

Points have carrier `cart(R,R)`. The functions `vec`, `dot`, `det`, and
`distance_sq` return displacements, scalar products, signed areas, and squared
lengths. Lines and circles are point sets; incidence and shape conditions are
`prop` relations. They do not select or construct a new point.

### Nondegenerate parallelograms

`$is_parallelogram(a,b,c,d)` means that the vertices, in boundary order, form
a nondegenerate parallelogram. Its definition requires
`$is_triangle(a,b,c)` and both pairs of parallel opposite sides. The triangle
condition excludes collinear points; parallelism also requires nonzero sides.
Rectangles, rhombi, and squares inherit this condition.

Two parallelism tests alone are insufficient: the collinear vertices
`(0,0),(1,0),(4,0),(2,0)` pass them even though their diagonal midpoints differ.
Coordinate lemmas that assume the affine identity `d = a + c - b`
componentwise retain those explicit hypotheses and may still cover degenerate
coordinate configurations. The predicate and those algebraic lemmas have
different domains.

### Internal angle bisectors

`$is_angle_bisector(a,b,c,d)` means that the ray from `b` through `d`
internally bisects the nondegenerate angle `abc`. The defining clauses are
noncollinearity of `a,b,c`, congruence of angles `abd` and `dbc`, and
`angle_cos_num(a,b,d) > 0`.

Angle congruence supplies nonzero arms and equality of the signed cosines.
For a nondegenerate angle, the internal half-angle is acute; the positive
dot product selects this ray. The reverse ray has equal obtuse angles and
fails that condition. Zero and straight angles are excluded by noncollinearity.
The point `d` need not lie on the opposite segment; any nonzero point on the
internal ray is allowed. This relation does not construct that point.

## Dependencies and verification boundaries

Coordinate functions precede incidence and angle relations; triangle
nondegeneracy and parallelism precede quadrilateral shapes. Preserve this
definition order in both entrypoints.

The executable cases in `definition_boundaries/main.lit` use the actual
definitions, a rectangle, the collinear counterexample, both orientations
of a right-angle bisector, and an obtuse angle's internal bisector. They also
check general nondegeneracy consequences.
All defining clauses and these acceptance proofs must remain free of user
`trust` and axioms. No Lean compilation is established by these native checks.
