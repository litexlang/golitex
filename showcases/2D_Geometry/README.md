# 2D Geometry in Litex

This collection develops plane geometry from real coordinate pairs, then uses
those definitions in selected IMO formalizations. Its mathematical thread runs
from displacement, dot product and determinant to incidence, triangle and circle
lemmas, and finally to construction, inequalities and counting arguments.

The geometry library is maintained by Jiachen Shen and Keyao Zhu. The contest
sources come from Jiachen Shen's published geometry formalizations. Problem
folder numbers retain the source collection's identifiers; the table below
gives their IMO year and official problem number.

## Coordinates become mathematical definitions

A point has carrier `cart(R,R)`, with coordinates `p(1)` and `p(2)`. A vector is
an ordinary function value whose components can be used in later calculations:

```litex
have fn vec(A,B cart(R,R)) cart(R,R) = (B(1)-A(1),B(2)-A(2))
have a,b cart(R,R)
vec(a,b)(1) = b(1)-a(1)
vec(a,b)(2) = b(2)-a(2)
```

Geometric relations retain their domains in their definitions. For example, a
segment has distinct endpoints and a parameter between zero and one:

```litex
prop is_on_segment(p,a,b cart(R,R)):
    a != b
    exist t R st {0 <= t, t <= 1, p(1) = (1-t)*a(1)+t*b(1), p(2) = (1-t)*a(2)+t*b(2)}
```

Declaring this relation does not assert that an arbitrary point lies on the
segment. A proof must establish its defining facts and supply the parameter.
This distinction lets the same vocabulary support both ordinary geometry and
the more demanding configurations in the contest examples.

## Coordinate calculations become reusable lemmas

The library makes the passage from a geometric operation to its scalar formula
explicit. Dot-product symmetry, for example, is proved by a calculation:

```litex
have fn dot(u,v cart(R,R)) R = u(1)*v(1)+u(2)*v(2)
thm dot_symmetric:
    ? forall u,v cart(R,R):
        dot(u,v) = dot(v,u)
    dot(u,v) = u(1)*v(1)+u(2)*v(2) = v(1)*u(1)+v(2)*u(2) = dot(v,u)
```

Later proofs reuse named coordinate, sign and distance lemmas. Lines and
circles are sets of points; incidence and angle conditions are predicates;
theorems justify the changes of representation between these descriptions.
Distinct endpoints, positive radii and nondegenerate triangles remain visible
where the corresponding interface requires them.

## Library entrypoints

| Source | Content |
|---|---|
| [geo_definitions.lit](geo_definitions.lit) | 40 foundational declarations: vectors, dot product, determinant, squared distance, lines, circles and geometric relations. |
| [geo.lit](geo.lit) | The same definitions followed by the checked distance function and 186 theorems, for 227 declarations in total. Topics include triangle congruence, affine geometry, circle criteria and length inequalities. |

Choose one library entrypoint. The complete `geo.lit` already contains the
entire definitions file. The IMO solutions below are independent developments
with their required mathematical vocabulary included locally.

## IMO examples

The seven problems below comprise nine solution packages, all checked in strict
mode with the 2026-10-06 release build used for this collection.

| IMO problem | Mathematical theme | Sources and coverage |
|---|---|---|
| 1960, Problem 6 | Cone, inscribed sphere and a sharp volume ratio | [Solution 1](IMO/problem_2/Solution-1/solution_part_b.lit) includes both parts and an attaining configuration. [Solution 2](IMO/problem_2/Solution-2/solution_part_a.lit) is the alternative for part (a). This solid-geometry application is reduced to its plane axial section and scalar relations. |
| 1961, Problem 4 | Interior points, barycentric weights and cevian ratios | [Both ratio bounds](IMO/problem_3/solution.lit), with incidence and noncollinearity retained. |
| 1961, Problem 5 | Triangle construction from two sides and a median-angle condition | [Necessity, construction and equality cases](IMO/problem_4/solution.lit). |
| 1962, Problem 6 | Circumcenter, incenter and Euler's distance relation | [Scalar alternative](IMO/problem_5/Solution-1/solution.lit) and [full geometric configuration](IMO/problem_5/Solution-2/solution.lit). The latter derives the circle data before proving the squared and principal-root identities. |
| 1963, Problem 3 | An equiangular polygon with monotone side lengths | [Normalized side-chain proof](IMO/problem_7/solution.lit). The formal interface uses the source's trigonometric closure equations. |
| 1966, Problem 6 | Small triangles cut off by three interior side points | [Area bound](IMO/problem_12/solution.lit), expressed through squared unsigned areas. |
| 1968, Problem 1 | Consecutive integer side lengths and a doubled angle | [Unique-existence proof](IMO/problem_15/solution.lit), with the witness `(4,5,6)` and all angle-order alternatives. |

Read the theorem's actual assumptions and conclusion when using a result. The
scalar and normalized variants expose their chosen mathematical models; they
should not be mistaken for additional geometric constructions that their
statements do not provide.

Each problem or solution variant has its own small `litex.config` so its files
are loaded in the required order. The collection contains the Litex sources,
those execution configs and this README; development records stay with the
source workspace.

With `litex` on your path, run these commands from this directory:

```sh
litex -strict -f geo.lit
litex -strict -r IMO/problem_2/Solution-1
```

The first checks the complete geometry library. The second loads an IMO
solution's definitions and proofs in its configured order. Use the directory
of another problem or solution variant to check that development instead.
