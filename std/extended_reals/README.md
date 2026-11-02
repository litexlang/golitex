# Extended real order and extrema

This module covers Tao Analysis I 5.5 and 6.2. It retains literal native R,
adjoins two proved distinct nonreal values, and defines total negation, order
and extrema on the extended carrier. The original real-subset supremum and
native finite completeness interfaces retain their contracts.

```ini
[import std]
Extended = extended_reals
[alias]
xreal = Extended::main
[export]
main = "./main.lit"
```

All names below follow xreal::. The existing markers use the proved bounded
Russell diagonal outside R and outside R union {first marker}; finite real
values retain their literal identity. No tagged real copy or new axiom is used.

| Interface | Fixed contract |
| --- | --- |
| ExtendedReal; real_positive_infinity; real_negative_infinity | Native R plus two distinct nonreal values, with exhaustive finite/positive/negative cases. |
| is_finite_extended_real; is_infinite_extended_real | Membership in R; equality to either infinity. |
| extended_real_negate(x) | Native -x when finite; exchange the two infinity markers. |
| extended_real_le(x,y); extended_real_lt(x,y) | Finite native order together with negative/positive infinity endpoints; strict order additionally requires x!=y. |
| is_real_set_upper_bound(E,M); is_real_set_bounded_above(E) | Real subset and real bound; existential real boundedness. |
| extended_real_sup(E) | Input power_set(R), output ExtendedReal: empty -> negative infinity; nonempty unbounded above -> positive infinity; otherwise native finite sup(E). |
| extended_set_supremum(E) | Input power_set(ExtendedReal), output ExtendedReal: positive infinity when present, otherwise the old real-subset supremum of intersect(E,R). |
| \extended_negated_set<E> | Actual range of negation on the complete E domain. |
| extended_set_infimum(E) | Negation of the supremum of that actual negated image. |
| is_extended_set_upper_bound(E,M); is_extended_set_lower_bound(E,M) | Arbitrary extended set and extended upper/lower bound. |

The order is reflexive, antisymmetric, transitive and total. Trichotomy has
exclusive strict/equal alternatives. Negation is involutive and reverses
order. The finite-order branch uses actual real witnesses, keeping native real
comparisons in their real domains.

For every x in E, extended_set_supremum_bounds_members and
extended_set_infimum_bounds_members give the upper/lower value bounds.
extended_set_supremum_le_upper_bound and extended_set_infimum_ge_lower_bound
compare with every extended bound, including both infinities. Maximum/minimum
specializations consume actual members and bound proofs. Source case 6.2.6(c)
is proved exactly: without positive infinity, removing negative infinity leaves
a real set and gives the same supremum as the original real-subset operation.

Publish carrier evidence before constructing a set-valued argument or writing
a goal that uses it. real_numbers_subset_extended_reals and
real_set_is_extended_real_set supply finite inclusion; the infinity membership
theorems supply the additional values. The examples show explicit real-set and
union carrier proofs on the actual domains.

## Real-subset compatibility example

Native sup(E) consumes a finite least-upper-bound certificate. The total
extended_real_sup(E) takes every real subset, including empty and unbounded
sets. This complete existing caller remains valid:

```litex
release obj def xreal::extended_real_sup
release thm xreal::extended_real_sup_empty_value
xreal::extended_real_sup({}) = xreal::real_negative_infinity
release thm xreal::extended_real_sup_reals_value
xreal::extended_real_sup(R) = xreal::real_positive_infinity
have unit_interval set = {x R:0 <= x and x <= 1}
unit_interval $subset R
unit_interval $in power_set(R)
1 $in unit_interval
claim:
    ? forall x unit_interval:
        x <= 1
    x <= 1
by def $xreal::is_real_set_upper_bound(unit_interval,1)
release thm xreal::extended_real_sup_equals_maximum(unit_interval,1)
xreal::extended_real_sup(unit_interval) = 1
```

## Infinite-element example

All negative integers together with negative infinity have supremum -1 and
infimum negative infinity. The empty set has the opposite two extremal values.
This complete caller opens the imported value functions and supplies the actual
set and all carrier/bound evidence:

```litex
release obj def xreal::extended_real_sup
release obj def xreal::extended_real_negate
release obj def xreal::extended_set_supremum
release obj def xreal::extended_set_infimum
release thm xreal::real_numbers_subset_extended_reals

release thm xreal::negative_infinity_is_extended_real

claim:
    ? {n Z:n<=-1} $in power_set(R)
    claim:
        ? forall x {n Z:n<=-1}:
            x $in R
        x $in Z
        x $in R
    by def {n Z:n<=-1} $subset R
    {n Z:n<=-1} $in power_set(R)

have negative_integer_example power_set(R) = {n Z:n<=-1}

release thm xreal::real_set_is_extended_real_set(negative_integer_example)

claim:
    ? union(negative_integer_example,{xreal::real_negative_infinity}) $in power_set(xreal::ExtendedReal)
    claim:
        ? forall x union(negative_integer_example,{xreal::real_negative_infinity}):
            x $in xreal::ExtendedReal
        by cases:
            ? x $in xreal::ExtendedReal
            case x $in negative_integer_example:
                negative_integer_example $subset R
                x $in R
                R $subset xreal::ExtendedReal
                x $in xreal::ExtendedReal
            case x $in {xreal::real_negative_infinity}:
                x=xreal::real_negative_infinity
                xreal::real_negative_infinity $in xreal::ExtendedReal
                x $in xreal::ExtendedReal
    by def union(negative_integer_example,{xreal::real_negative_infinity}) $subset xreal::ExtendedReal
    union(negative_integer_example,{xreal::real_negative_infinity}) $in power_set(xreal::ExtendedReal)

have negative_integer_extended_example power_set(xreal::ExtendedReal) = union(negative_integer_example,{xreal::real_negative_infinity})

-1 $in negative_integer_example

-1 $in negative_integer_extended_example

claim:
    ? $xreal::is_extended_set_upper_bound(negative_integer_extended_example,-1)
    claim:
        ? forall x negative_integer_extended_example:
            $xreal::extended_real_le(x,-1)
        negative_integer_extended_example=union(negative_integer_example,{xreal::real_negative_infinity})
        x $in union(negative_integer_example,{xreal::real_negative_infinity})
        by cases:
            ? $xreal::extended_real_le(x,-1)
            case x $in negative_integer_example:
                negative_integer_example={n Z:n<=-1}
                x $in Z
                x $in R
                x<=-1
                release thm xreal::real_order_is_extended_real_order(x,-1)
            case x $in {xreal::real_negative_infinity}:
                x=xreal::real_negative_infinity
                release thm xreal::negative_infinity_le_extended_real(-1)
                $xreal::extended_real_le(x,-1)
    by def $xreal::is_extended_set_upper_bound(negative_integer_extended_example,-1)

release thm xreal::extended_set_supremum_equals_maximum(negative_integer_extended_example,-1)

xreal::extended_set_supremum(negative_integer_extended_example)=-1

xreal::real_negative_infinity $in negative_integer_extended_example

claim:
    ? $xreal::is_extended_set_lower_bound(negative_integer_extended_example,xreal::real_negative_infinity)
    claim:
        ? forall x negative_integer_extended_example:
            $xreal::extended_real_le(xreal::real_negative_infinity,x)
        negative_integer_extended_example $subset xreal::ExtendedReal
        x $in xreal::ExtendedReal
        release thm xreal::negative_infinity_le_extended_real(x)
    by def $xreal::is_extended_set_lower_bound(negative_integer_extended_example,xreal::real_negative_infinity)

release thm xreal::extended_set_infimum_equals_minimum(negative_integer_extended_example,xreal::real_negative_infinity)

xreal::extended_set_infimum(negative_integer_extended_example)=xreal::real_negative_infinity

release thm xreal::extended_set_supremum_empty

release thm xreal::extended_set_infimum_empty
```

Native real order, native finite sup/inf and scalar negation keep their original
domains. Extended values use the distinct source interfaces above. The source
defines no infinity addition or multiplication here. There are no new native
features, kernel/WD changes, axioms, trust declarations or alternative real
models. Exact source correspondence and strict consumers remain in experiments/.
