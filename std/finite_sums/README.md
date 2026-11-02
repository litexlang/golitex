# Finite real sums

This module covers Tao Analysis I 7.1.1, 7.1.4, 7.1.6, 7.1.8, 7.1.11,
7.1.13 and 7.1.14, with the author's corrections. It supplies total integer
interval sums, enumeration independence, finite-set sum laws and finite Fubini.
All function data retains its actual original domain.

Use finite_set_sum(closed_range(m,n),a) for the source interval sum, including
n<m and its actual empty-domain function. Native sum(m,n,a) keeps its existing
m<=n contract; finite_real_interval_sum_nonempty_native proves the bridge.
The recurrence includes the first term n=m-1. Splitting assumes m<=n+1 and
n<=p, permitting either piece to be empty. Addition, scaling, triangle,
comparison and translation allow every integer m,n, including empty intervals.

| Interface after fs:: | Role |
| --- | --- |
| finite_real_interval_sum_empty, finite_real_interval_sum_singleton | Empty and one-term values. |
| finite_real_interval_sum_successor, finite_real_interval_sum_split | Source recurrence and corrected splitting. |
| finite_real_interval_sum_add, finite_real_interval_sum_scale, finite_real_interval_sum_triangle, finite_real_interval_sum_comparison | Complete interval laws. |
| integer_interval_unshift_index, integer_interval_unshift_bijective, finite_real_interval_sum_shift | Actual inverse translation, bijection and literal shifted summands. |
| finite_set_bijective_enumeration_exists | Actual bijective enumeration, including the empty set. |
| finite_real_set_sum_enumeration, finite_real_set_sum_enumeration_independent | Every bijective enumeration gives the same sum. |
| finite_real_set_sum_substitution | Arbitrary finite bijective reindexing. |
| finite_real_set_sum_substitution_on_superset, finite_real_set_sum_enumeration_on_superset | The original function may be defined on a larger set U. |
| finite_real_set_sum_empty, finite_real_set_sum_singleton, finite_real_set_sum_disjoint_union | Basic finite-set decompositions. |
| finite_real_set_sum_add, finite_real_set_sum_scale, finite_real_set_sum_comparison, finite_real_set_sum_triangle | Finite-set linearity, order and triangle. |
| cartesian_pair_swap_map, cartesian_pair_swap_bijective | Actual coordinate swap on arbitrary Cartesian sets. |
| finite_real_cartesian_sum_flatten, finite_real_cartesian_sum_swap, finite_real_sum_fubini | Nested/flat and reversed-order equalities, including empty factors. |

The example checks an empty interval, recurrence at the first term, both empty
split boundaries, negative translation, a weighted rectangle with total 30,
and finite Fubini with an empty factor:

```ini
[import std]
FiniteSums = finite_sums
[alias]
fs = FiniteSums::main
[export]
main = "./main.lit"
```

```litex
have fn empty_data(k closed_range(4,1)) R=k

release thm fs::finite_real_interval_sum_empty(4,1,empty_data)

finite_set_sum(closed_range(4,1),empty_data)=0

have fn first_values(k closed_range(-2,(-3)+1)) R=7

release thm fs::integer_closed_interval_nested_subset(-2,-3,-2,(-3)+1)

(-3)+1 $in closed_range(-2,(-3)+1)

release thm fs::finite_real_interval_sum_successor(-2,-3,first_values)

finite_set_sum(closed_range(-2,(-3)+1),first_values)=7

have fn squares(k closed_range(-2,2)) R=k^2

release thm fs::integer_closed_interval_nested_subset(-2,-3,-2,2)

release thm fs::integer_closed_interval_nested_subset((-3)+1,2,-2,2)

release thm fs::integer_closed_interval_nested_subset(2+1,2,-2,2)

release thm fs::finite_real_interval_sum_split(-2,-3,2,squares)

release thm fs::finite_real_interval_sum_split(-2,2,2,squares)

release thm fs::finite_real_interval_sum_shift(-2,2,-5,squares)

finite_set_sum(closed_range(-2,2),squares)=10

have fn zero_function(x {}) R=0

release thm fs::finite_real_set_sum_empty({},zero_function)

release thm fs::finite_set_bijective_enumeration_exists({})

claim:
    ? forall p cart(closed_range(-1,1),closed_range(2,3)):
        p(1) $in R
        p(2) $in R
    p(1) $in closed_range(-1,1)
    p(2) $in closed_range(2,3)
    p(1) $in Z
    p(2) $in Z
    p(1) $in R
    p(2) $in R

claim:
    ? forall p cart(closed_range(-1,1),closed_range(2,3)):
        p(1)+2*p(2) $in R
    p(1) $in R
    p(2) $in R
    2*p(2) $in R
    p(1)+2*p(2) $in R

have fn weights(p cart(closed_range(-1,1),closed_range(2,3))) R=p(1)+2*p(2)

release thm fs::finite_real_sum_fubini(closed_range(-1,1),closed_range(2,3),weights)

claim:
    ? weights((-1,2))=3 and weights((-1,3))=5 and weights((0,2))=4 and weights((0,3))=6 and weights((1,2))=5 and weights((1,3))=7
    (-1,2)(1)=-1
    (-1,2)(2)=2
    2*(-1,2)(2)=2*2
    weights((-1,2))=(-1,2)(1)+2*(-1,2)(2)
    (-1,2)(1)+2*(-1,2)(2)=-1+2*(-1,2)(2)
    -1+2*(-1,2)(2)=-1+2*2=3
    weights((-1,2))=3
    (-1,3)(1)=-1
    (-1,3)(2)=3
    2*(-1,3)(2)=2*3
    weights((-1,3))=(-1,3)(1)+2*(-1,3)(2)
    (-1,3)(1)+2*(-1,3)(2)=-1+2*(-1,3)(2)
    -1+2*(-1,3)(2)=-1+2*3=5
    weights((-1,3))=5
    (0,2)(1)=0
    (0,2)(2)=2
    2*(0,2)(2)=2*2
    weights((0,2))=(0,2)(1)+2*(0,2)(2)
    (0,2)(1)+2*(0,2)(2)=0+2*(0,2)(2)
    0+2*(0,2)(2)=0+2*2=4
    weights((0,2))=4
    (0,3)(1)=0
    (0,3)(2)=3
    2*(0,3)(2)=2*3
    weights((0,3))=(0,3)(1)+2*(0,3)(2)
    (0,3)(1)+2*(0,3)(2)=0+2*(0,3)(2)
    0+2*(0,3)(2)=0+2*3=6
    weights((0,3))=6
    (1,2)(1)=1
    (1,2)(2)=2
    2*(1,2)(2)=2*2
    weights((1,2))=(1,2)(1)+2*(1,2)(2)
    (1,2)(1)+2*(1,2)(2)=1+2*(1,2)(2)
    1+2*(1,2)(2)=1+2*2=5
    weights((1,2))=5
    (1,3)(1)=1
    (1,3)(2)=3
    2*(1,3)(2)=2*3
    weights((1,3))=(1,3)(1)+2*(1,3)(2)
    (1,3)(1)+2*(1,3)(2)=1+2*(1,3)(2)
    1+2*(1,3)(2)=1+2*3=7
    weights((1,3))=7

claim:
    ? finite_set_sum(closed_range(2,3),fn(y closed_range(2,3)) R {weights((-1,y))})=8 and finite_set_sum(closed_range(2,3),fn(y closed_range(2,3)) R {weights((0,y))})=10 and finite_set_sum(closed_range(2,3),fn(y closed_range(2,3)) R {weights((1,y))})=12
    finite_set_sum(closed_range(2,3),fn(y closed_range(2,3)) R {weights((-1,y))})=8
    finite_set_sum(closed_range(2,3),fn(y closed_range(2,3)) R {weights((0,y))})=10
    finite_set_sum(closed_range(2,3),fn(y closed_range(2,3)) R {weights((1,y))})=12

claim:
    ? finite_set_sum(cart(closed_range(-1,1),closed_range(2,3)),weights)=30
    finite_set_sum(closed_range(-1,1),fn(x closed_range(-1,1)) R {finite_set_sum(closed_range(2,3),fn(y closed_range(2,3)) R {weights((x,y))})})=30
    finite_set_sum(cart(closed_range(-1,1),closed_range(2,3)),weights)=finite_set_sum(closed_range(-1,1),fn(x closed_range(-1,1)) R {finite_set_sum(closed_range(2,3),fn(y closed_range(2,3)) R {weights((x,y))})})=30

have fn empty_rectangle(p cart({},closed_range(2,3))) R=0

release thm fs::finite_real_sum_fubini({},closed_range(2,3),empty_rectangle)

finite_set_sum(cart({},closed_range(2,3)),empty_rectangle)=0
```

For dependent endpoint domains, declare the actual function on the complete
endpoint expression used by the theorem. Publish the relevant interval subset,
endpoint membership and scalar output facts before using partial applications.
For Cartesian data, f has one tuple argument. The inverse substitution in
Fubini is the actual map from YxX to XxY; no binary-function convention is used.

Proof basis: existing native finite-set aggregation, exact set partitions,
actual bijections, existing finite enumeration and ordinary source proofs.
This is a source interface and compatibility layer over those native foundations.
The module has 38 statements: 31 named theorems, two actual function templates
and five supporting carrier claims. Strict source, complete imported contracts,
README applications, fresh applications and 22 negative controls are recorded
in experiments/. No new axiom, trust, native source change or build is included.
General membership verification and evidence composition/reuse belong to shared verify.
