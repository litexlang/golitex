# Metric spaces

This module contains a bundled metric-space interface, actual balls and metric
maps, with 13 checked source theorems. `MetricSpace<Ambient>` owns an actual
carrier contained in Ambient and a real-valued distance on its square.
Nonnegativity, diagonal zero, separation, symmetry and the triangle inequality
are direct laws. Empty carriers are permitted; pseudometrics are not metrics.

## Interfaces and results

| Interface | Contract and checked mathematics |
| --- | --- |
| `open_ball<A,M>(center,r)` | Actual subset, with r positive. Contains its center, is nested in radius and admits interior subballs. |
| `closed_ball<A,M>(center,r)` | Actual subset, with r nonnegative. At radius zero it is exactly the center singleton; the corresponding open ball is contained in it. |
| Distance estimates | Distinct points have positive distance. Reverse triangle inequality holds. If r+s<=d(x,y), the two open balls are disjoint; distinct points admit disjoint balls. |
| `is_lipschitz_map(A,M,B,T,f,L)` | L is nonnegative and the complete map satisfies d(f(x),f(y))<=L*d(x,y). Composite constants multiply. |
| `is_metric_continuous_at(A,M,B,T,f,p)` | For every positive epsilon there is a positive delta whose source ball is contained in the inverse image of the target ball. |
| `lipschitz_implies_metric_continuity` | Uses delta=epsilon/(L+1), covering L=0. |
| `real_line_distance(x,y)` | abs(x-y) on all reals. `real_line_metric_laws()` proves the complete metric structure membership. |

Import `metric` and alias its `main` export, for example `m = metric::main`.
Template applications use `\m::open_ball<A,M>(center,r)`. To construct the
real line, release `m::real_line_distance`'s object definition, call
`m::real_line_metric_laws()`, then bind `(R,m::real_line_distance)` as a
`MetricSpace<R>`. The validation consumer shows the complete field and
function-signature releases needed by downstream applications.

## Verification and boundaries

Run `python3 std/metric/validation/check.py` from the repository root.
The strict source has 19 accepted declarations; its imported consumer has
33 accepted statements, including the real line, doubling with L=2, a constant
map with L=0, an empty metric space and arbitrary-carrier theorem callers.
Six final-statement controls reject a missing Lipschitz bound, a negative
closed radius, a negative Lipschitz constant, separation of identical points,
zero distance on two distinct points and a zero open radius. Every preceding
statement must succeed.

The native scalar `is_lipschitz` predicate retains its existing contract;
`is_lipschitz_map` names the supplied-metric interface. No topology generated
by balls, sequence/Cauchy theory, completeness, compactness or fixed-point
result is supplied yet. See [math_collections.md](math_collections.md).
