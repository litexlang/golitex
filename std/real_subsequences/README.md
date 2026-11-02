# Real subsequences and compactness

This module covers Tao Analysis I 6.6.1, 6.6.4-6.6.6 and 6.6.8. Original and
subsequence data retain their complete integer tails {j Z:j>=start} and
{j Z:j>=substart}; both starts may be any integers. Limits and limit points
are finite real values with the existing closed-epsilon source definitions.

An increasing index map is an actual integer-valued function on the full
subsequence tail. Its definition requires every value >=start and each
successor value strictly greater than its predecessor. These two invariants
make it exactly a strictly increasing map into the original index tail.
The given-map relation requires unconditional b(n)=a(f(n)); the subsequence
relation asserts existence of such a map. Convergence is a proved consequence.

| Interface after sb:: | Mathematical use |
| --- | --- |
| is_increasing_integer_tail_index_map(start,substart,f) | Complete original-range and adjacent strict-order contract. |
| is_real_tail_subsequence_indexing(start,a,substart,b,f) | Supplied actual index map and exact value agreement. |
| is_real_tail_subsequence(start,a,substart,b) | Existential source relation; reflexive and transitive. |
| \real_tail_index_pullback<start,a,substart,f> | Actual a(f(n)) function for a valid increasing map. |
| real_tail_subsequence_preserves_limit | Full arbitrary-start limit preservation. |
| all_real_tail_subsequences_have_limit | Universal condition equivalent to the original limit. |
| least_natural_member(X) | Canonical minimum of a nonempty natural-number subset, from proved unique existence. |
| \real_tail_limit_point_indices<start,a,L,substart> | Actual recursive strictly increasing original indices, guarded by source limit-pointhood. |
| \real_tail_limit_point_subsequence<start,a,L,substart> | Actual selected data tending to the given finite limit point. |
| real_tail_subsequence_limit_is_limit_point | Every convergent subsequence yields an original limit point. |
| bounded_real_tail_has_convergent_subsequence | Bolzano-Weierstrass, returning an actual subsequence with finite limit equal to the original limsup. |

This complete example has a bounded, nonconvergent parent, actual subsequences
tending to both 1 and -1, and a negative subsequence start. Convergence is
published before selected limit values are used.

```ini
[import std]
Subsequences = real_subsequences
Real = real_sequences
Limits = real_sequence_limsup
Extrema = real_sequence_extrema
Extended = extended_reals
Approximation = real_approximation
Naturals = natural_numbers
[alias]
sb = Subsequences::main
rs = Real::main
rsl = Limits::main
sext = Extrema::main
xreal = Extended::main
approx = Approximation::main
nat = Naturals::main
[export]
main = "./main.lit"
```

```litex
have fn alternating_tail(n {j Z:j>=0}) R=(-1)^n

claim:
    ? forall n {j Z:j>=0}:
        abs(alternating_tail(n))=1
        -1<=alternating_tail(n)<=1
    n $in Z
    n>=0
    alternating_tail(n)=(-1)^n
    release thm approx::absolute_value_integer_power(-1,n)
    abs((-1)^n)=abs(-1)^n=1^n=1
    abs(alternating_tail(n))=1
    release thm approx::absolute_value_two_sided_bounds(alternating_tail(n),1)

claim:
    ? $rsl::is_real_tail_limit_point(0,alternating_tail,1)
    claim:
        ? forall epsilon R+,cutoff {j Z:j>=0}:
            exist n {j Z:j>=0} st {n>=cutoff and $approx::is_epsilon_close(alternating_tail(n),1,epsilon)}
        cutoff>=0
        cutoff $in N
        have n Z=2*cutoff
        n>=cutoff>=0
        n $in {j Z:j>=0}
        (-1)^(2*cutoff)=((-1)^2)^cutoff=1^cutoff=1
        alternating_tail(n)=(-1)^n=1
        abs(alternating_tail(n)-(1))=0<=epsilon
        by def $approx::is_epsilon_close(alternating_tail(n),1,epsilon)
        witness exist index {j Z:j>=0} st {index>=cutoff and $approx::is_epsilon_close(alternating_tail(index),1,epsilon)} from n
    release thm rsl::real_tail_arbitrarily_late_close_is_limit_point(0,alternating_tail,1)

claim:
    ? $rsl::is_real_tail_limit_point(0,alternating_tail,-1)
    claim:
        ? forall epsilon R+,cutoff {j Z:j>=0}:
            exist n {j Z:j>=0} st {n>=cutoff and $approx::is_epsilon_close(alternating_tail(n),-1,epsilon)}
        cutoff>=0
        cutoff $in N
        have n Z=2*cutoff+1
        cutoff+1>=0
        n=2*cutoff+1=cutoff+(cutoff+1)>=cutoff+0=cutoff
        n>=cutoff>=0
        n $in {j Z:j>=0}
        (-1)^(2*cutoff)=((-1)^2)^cutoff=1^cutoff=1
        (-1)^(2*cutoff+1)=(-1)^(2*cutoff)*(-1)^1=1*(-1)=-1
        alternating_tail(n)=(-1)^n=-1
        abs(alternating_tail(n)-(-1))=0<=epsilon
        by def $approx::is_epsilon_close(alternating_tail(n),-1,epsilon)
        witness exist index {j Z:j>=0} st {index>=cutoff and $approx::is_epsilon_close(alternating_tail(index),-1,epsilon)} from n
    release thm rsl::real_tail_arbitrarily_late_close_is_limit_point(0,alternating_tail,-1)

claim:
    ? $rs::is_bounded_real_tail(0,alternating_tail)
    claim:
        ? forall n {j Z:j>=0}:
            abs(alternating_tail(n))<=1
        abs(alternating_tail(n))=1
        abs(alternating_tail(n))<=1
    by def $rs::is_real_tail_bounded_by(0,alternating_tail,1)
    witness $rs::is_bounded_real_tail(0,alternating_tail) from 1

release thm sb::bounded_real_tail_has_convergent_subsequence(0,alternating_tail,0)

release thm sb::real_tail_limit_point_selected_is_subsequence(0,alternating_tail,1,0)

release thm sb::real_tail_limit_point_selected_subsequence_limit(0,alternating_tail,1,0)

release thm sb::real_tail_limit_point_selected_is_subsequence(0,alternating_tail,-1,-4)

release thm sb::real_tail_limit_point_selected_subsequence_limit(0,alternating_tail,-1,-4)

release thm rs::real_tail_limit_implies_convergent(0,\sb::real_tail_limit_point_subsequence<0,alternating_tail,1,0>,1)

release thm rs::real_tail_limit_value(0,\sb::real_tail_limit_point_subsequence<0,alternating_tail,1,0>,1)

\rs::real_tail_limit<0>(\sb::real_tail_limit_point_subsequence<0,alternating_tail,1,0>)=1

release thm rs::real_tail_limit_implies_convergent(-4,\sb::real_tail_limit_point_subsequence<0,alternating_tail,-1,-4>,-1)

release thm rs::real_tail_limit_value(-4,\sb::real_tail_limit_point_subsequence<0,alternating_tail,-1,-4>,-1)

\rs::real_tail_limit<-4>(\sb::real_tail_limit_point_subsequence<0,alternating_tail,-1,-4>)=-1

claim:
    ? not $rs::is_convergent_real_tail(0,alternating_tail)
    by contra:
        ? not $rs::is_convergent_real_tail(0,alternating_tail)
        obtain L from $rs::is_convergent_real_tail(0,alternating_tail)
        release thm rsl::real_tail_limit_point_unique_of_limit(0,alternating_tail,L,1)
        release thm rsl::real_tail_limit_point_unique_of_limit(0,alternating_tail,L,-1)
        1=L=-1
        impossible 1=-1
```

The selected indices come from least eligible natural offsets. Ordinary
induction proves natural well-ordering, uniqueness gives the canonical minimum,
and the existing natural_numbers recursion constructs all offsets. At step k,
the actual error is <=1/(k+1); offsets increase strictly. An Archimedean cutoff
proves the source epsilon limit at every integer subsequence start. No choice
function, new axiom or trust is introduced.

For direct minimum evaluation, release obj def sb::least_natural_member, publish
the exact nonempty natural-subset argument, and use its least-member relation.
Explicit original-index memberships precede quantified application goals.
General expression verification and evidence composition/reuse remain shared
verify responsibilities; no native or scenario-specific WD change is made.

The module has 47 source statements: 24 named theorems, six propositions, nine
actual function templates, one canonical minimum function and seven supporting
carrier proofs. Strict saved-source, full imported-contract, complete-example,
unequal-start and false-case evidence is retained under experiments/. Native
N/Z/R, ordinary induction, and the checked sequence/extremal-limit libraries
are reused. This is a real-sequence result; it does not claim general metric
compactness, infinite limit points, or a Lean replay.
