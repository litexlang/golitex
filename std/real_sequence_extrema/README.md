# Extrema and monotone convergence of real sequences

Sequences retain their entire domain `{j Z:j>=start}` for any integer start.
`\real_tail_supremum<start>(a)` and `\real_tail_infimum<start>(a)` apply
the existing total extended-set extrema to the actual native `fn_range(a)`.
Their codomain is `extended_reals::ExtendedReal`, including infinite values.
Native R, the one-argument native lim and all existing public names keep their
contracts.

```ini
[import std]
Extrema = real_sequence_extrema
Real = real_sequences
Extended = extended_reals
[alias]
sext = Extrema::main
rs = Real::main
xreal = Extended::main
[export]
main = "./main.lit"
```

Upper/lower bounds are independent real one-sided bounds. Increasing and
decreasing mean adjacent nonstrict inequalities on the original tail;
monotone means either direction. The public offset-index helper and induction
prove pairwise monotonicity. Supply original-domain and real-value facts before
forming successor-valued goals.

Every sequence member is bounded by its extended extrema. Leastness and
greatestness quantify over every extended bound. Strict approach theorems use
any extended comparison value y: y below the supremum yields an actual original
index above y, with the exact dual for the infimum. No boundedness restriction
is imposed on these statements.

A finite upper bound makes the supremum real; a finite lower bound makes the
infimum real. Increasing/upper-bounded and decreasing/lower-bounded convergence
theorems construct an actual real limit, identify it exactly with the extremum
and retain the one-sided bound. Separate convergence and selected-limit laws
permit the guarded `\rs::real_tail_limit<start>(a)`. For monotone sequences,
boundedness implies convergence; the converse is the existing real_sequences
convergent-to-bounded theorem.

This complete example proves supremum 1, infimum 0 and convergence of 1/n on
n>=1, and proves that the infimum is absent from its actual range. Imported plain
value functions are explicitly opened before evaluation, the successor domain
is proved before its comparison, and convergence precedes selection.

```litex
release obj def xreal::extended_real_sup

release obj def xreal::extended_real_negate

release obj def xreal::extended_set_supremum

release obj def xreal::extended_set_infimum

release obj def rs::positive_real_reciprocal_tail

claim:
    ? $sext::is_real_tail_upper_bound(1,rs::positive_real_reciprocal_tail,1)
    claim:
        ? forall n {j Z:j>=1}:
            rs::positive_real_reciprocal_tail(n)<=1
        n>=1
        n>0
        rs::positive_real_reciprocal_tail(n)=1/n
        1/n<=n/n=1
    by def $sext::is_real_tail_upper_bound(1,rs::positive_real_reciprocal_tail,1)

claim:
    ? $sext::is_real_tail_lower_bound(1,rs::positive_real_reciprocal_tail,0)
    claim:
        ? forall n {j Z:j>=1}:
            0<=rs::positive_real_reciprocal_tail(n)
        n>=1
        n>0
        rs::positive_real_reciprocal_tail(n)=1/n>0
    by def $sext::is_real_tail_lower_bound(1,rs::positive_real_reciprocal_tail,0)

claim:
    ? forall n {j Z:j>=1}:
        n+1 $in {j Z:j>=1}
    release thm sext::real_tail_natural_offset_member(1,n,1)

claim:
    ? $sext::is_decreasing_real_tail(1,rs::positive_real_reciprocal_tail)
    claim:
        ? forall n {j Z:j>=1}:
            rs::positive_real_reciprocal_tail(n+1)<=rs::positive_real_reciprocal_tail(n)
        n>=1
        n>0
        n+1 $in {j Z:j>=1}
        n+1>0
        rs::positive_real_reciprocal_tail(n+1) $in R
        rs::positive_real_reciprocal_tail(n) $in R
        n*(n+1)>0
        n<=n+1
        n/(n*(n+1))<=(n+1)/(n*(n+1))
        rs::positive_real_reciprocal_tail(n+1)=1/(n+1)=n/(n*(n+1))
        rs::positive_real_reciprocal_tail(n)=1/n=(n+1)/(n*(n+1))
        rs::positive_real_reciprocal_tail(n+1)<=rs::positive_real_reciprocal_tail(n)
    by def $sext::is_decreasing_real_tail(1,rs::positive_real_reciprocal_tail)

release thm sext::upper_bounded_real_tail_has_real_supremum(1,rs::positive_real_reciprocal_tail,1)

release thm sext::lower_bounded_real_tail_has_real_infimum(1,rs::positive_real_reciprocal_tail,0)

release thm sext::real_tail_upper_bound_is_extended(1,rs::positive_real_reciprocal_tail,1)

release thm sext::real_tail_supremum_le_upper_bound(1,rs::positive_real_reciprocal_tail,1)

release thm sext::real_tail_supremum_bounds_members(1,rs::positive_real_reciprocal_tail,1)

rs::positive_real_reciprocal_tail(1)=1

$xreal::extended_real_le(1,\sext::real_tail_supremum<1>(rs::positive_real_reciprocal_tail))

release thm xreal::extended_real_order_antisymmetric(1,\sext::real_tail_supremum<1>(rs::positive_real_reciprocal_tail))

\sext::real_tail_supremum<1>(rs::positive_real_reciprocal_tail)=1

release thm rs::positive_real_reciprocal_tail_limit

release thm rs::real_tail_limit_implies_convergent(1,rs::positive_real_reciprocal_tail,0)

release thm rs::real_tail_limit_value(1,rs::positive_real_reciprocal_tail,0)

release thm sext::decreasing_lower_bounded_real_tail_selected_limit(1,rs::positive_real_reciprocal_tail,0)

\sext::real_tail_infimum<1>(rs::positive_real_reciprocal_tail)=\rs::real_tail_limit<1>(rs::positive_real_reciprocal_tail)=0

claim:
    ? not 0 $in fn_range(rs::positive_real_reciprocal_tail)
    by contra:
        ? not 0 $in fn_range(rs::positive_real_reciprocal_tail)
        have by fn_preimage: n from 0 $in fn_range(rs::positive_real_reciprocal_tail)
        n>=1
        n>0
        rs::positive_real_reciprocal_tail(n)=1/n>0
        0=rs::positive_real_reciprocal_tail(n)
        impossible 0>0
```

The 43 source statements contain 28 named theorems, seven propositions, two
actual start-parameterized value functions, two supporting universal proofs
and four existing imported-function exposures. The source proofs use native
real arithmetic/completeness, sets/images/preimages and ordinary logic. There
are no new axioms, trust declarations, native rules or kernel/WD changes.

The corrected full ExtendedReal-valued sequence interface is provided by
[extended_sequence_extrema](../extended_sequence_extrema/README.md), including
an actual same-value embedding of a real sequence. This module keeps its fixed
real-valued input contracts and reuses the general strict set-approach proofs.

Tao Analysis I 6.3.10 reuses the existing stronger real_series geometric-limit
theorem in a separate checked consumer. That consumer constructs q^n on every
integer tail for 0<q<1 and proves its actual N+ reindex identity. This generic
module does not acquire a real_series dependency or repeat that proof.
