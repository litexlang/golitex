# Rearrangements of real series

For an actual complete real function `a` on `{j Z:j>=0}` and a bijection
`p:N->N`, this module proves Tao Analysis I 7.4.1 and 7.4.3 in their full
real-domain form:

- A convergent series with every original term nonnegative retains convergence
  and its sum after rearrangement.
- An absolutely convergent series retains absolute convergence and its signed
  sum after rearrangement.

The actual rearranged data is
`\rr::zero_start_real_index_composition<a,p>(n)=a(p(n))`.
The constructor accepts any natural index map; the rearrangement theorems
require bijectivity. It neither extends the original function nor changes its
complete domain. Native `N` includes zero.

| Interface after `rr::` | Contract |
| --- | --- |
| nonnegative_zero_start_series_rearrangement_candidate | Nonnegative original data, a bijection, and an original candidate `L` give the same actual rearranged candidate `L`. |
| nonnegative_zero_start_series_rearrangement_has_same_sum | The original nonnegative convergence guard suffices; the rearranged candidate is the existing guarded original sum. |
| absolutely_convergent_zero_start_series_rearrangement_converges_absolutely | Absolute convergence and a bijection give both absolute and ordinary rearranged convergence. |
| absolutely_convergent_zero_start_series_rearrangement_candidate | Under absolute convergence and bijectivity, every original signed candidate `L` is the actual rearranged candidate. |
| absolutely_convergent_zero_start_series_rearrangement_has_same_sum | Under the same conditions the rearranged candidate is the existing guarded original sum. |

The module also proves convergence for any injective natural index map of a
convergent nonnegative series, and that its sum cannot exceed the original.
Equality requires surjectivity. Actual finite-prefix restrictions, their finite
images and maxima, finite subset-sum comparison, inverse maps and partial-sum
bounds supply the proof. All original functions retain their complete domains.
The signed proof applies the nonnegative theorem to `abs(a)` and `a+abs(a)`,
then uses existing series algebra and uniqueness. This is an equivalent proof
of the complete source theorem; no assertion about conditionally convergent
rearrangements is included here.

The example below constructs an adjacent pair swap, proves its bijectivity,
and checks actual reordered terms and guarded sums for positive and signed
geometric series. The original signed sum and rearranged signed sum are `2/3`.
Every selector is used only after its convergence guard is proved.

```ini
[import std]
Rearrangements = real_series_rearrangements
Nonnegative = real_nonnegative_series
TailSeries = real_tail_series
Real = real_sequences
Extrema = real_sequence_extrema
Limits = real_sequence_limsup
FiniteSums = finite_sums
Cardinality = cardinality
Extended = extended_reals
[alias]
rr = Rearrangements::main
nn = Nonnegative::main
ts = TailSeries::main
rs = Real::main
sext = Extrema::main
limits = Limits::main
fs = FiniteSums::main
card = Cardinality::main
xreal = Extended::main
[export]
main = "./main.lit"
```

```litex
claim:
    ? forall n {j Z:j>=0}:
        n $in N
    n $in Z
    n>=0
    n $in N

claim:
    ? forall n N:
        n $in {j Z:j>=0}
    n $in Z
    n>=0
    n $in {j Z:j>=0}

claim:
    ? forall p fn(k N) N,n {j Z:j>=0}:
        p(n) $in {j Z:j>=0}
    n $in N
    p(n) $in N
    p(n) $in Z
    p(n)>=0
    p(n) $in {j Z:j>=0}

claim:
    ? forall M N,n closed_range(0,M):
        n $in N
        n $in {j Z:j>=0}
    n $in Z
    n>=0
    n $in N
    n $in {j Z:j>=0}

claim:
    ? forall p fn(k N) N,M N,n closed_range(0,M):
        \rr::natural_zero_prefix_restriction<p,M>(n) $in fn_range(\rr::natural_zero_prefix_restriction<p,M>)
    release thm fn_set_member(\rr::natural_zero_prefix_restriction<p,M>,fn(k closed_range(0,M)) N)
    \rr::natural_zero_prefix_restriction<p,M>(n) $in fn_range(\rr::natural_zero_prefix_restriction<p,M>)

claim:
    ? forall p fn(k N) N,M N:
        $is_finite_set(fn_range(\rr::natural_zero_prefix_restriction<p,M>))
    release thm fn_set_member(\rr::natural_zero_prefix_restriction<p,M>,fn(n closed_range(0,M)) N)
    release thm card::finite_image_size_bound(closed_range(0,M),N,\rr::natural_zero_prefix_restriction<p,M>)

claim:
    ? forall p fn(k N) N,M N:
        fn_range(\rr::natural_zero_prefix_restriction<p,M>) $subset {j Z:j>=0}
    release thm fn_set_member(\rr::natural_zero_prefix_restriction<p,M>,fn(n closed_range(0,M)) N)
    claim:
        ? forall x fn_range(\rr::natural_zero_prefix_restriction<p,M>):
            x $in {j Z:j>=0}
        have by fn_preimage: n from x $in fn_range(\rr::natural_zero_prefix_restriction<p,M>)
        x=\rr::natural_zero_prefix_restriction<p,M>(n)=p(n)
        n $in N
        p(n) $in N
        x $in N
        x $in {j Z:j>=0}
    by def fn_range(\rr::natural_zero_prefix_restriction<p,M>) $subset {j Z:j>=0}

claim:
    ? forall M N:
        closed_range(0,M) $subset {j Z:j>=0}
    claim:
        ? forall n closed_range(0,M):
            n $in {j Z:j>=0}
        n $in Z
        n>=0
        n $in {j Z:j>=0}
    by def closed_range(0,M) $subset {j Z:j>=0}

claim:
    ? forall a fn(n {j Z:j>=0}) R,p fn(k N) N,M N:
        finite_set_sum(fn_range(\rr::natural_zero_prefix_restriction<p,M>),a) $in R
    release thm fn_set_member(a,fn(n {j Z:j>=0}) R)
    $is_finite_set(fn_range(\rr::natural_zero_prefix_restriction<p,M>))
    fn_range(\rr::natural_zero_prefix_restriction<p,M>) $subset {j Z:j>=0}
    finite_set_sum(fn_range(\rr::natural_zero_prefix_restriction<p,M>),a) $in R

claim:
    ? forall a fn(n {j Z:j>=0}) R:
        $ts::is_absolutely_convergent_real_tail_series(0,a)
        =>:
            $ts::is_convergent_real_tail_series(0,a)
    release thm ts::absolutely_convergent_real_tail_series_converges(0,a)

claim:
    ? forall n N:
        n%2=0 or n%2=1
    n $in Z
    n%2 $in Z
    n%2>=0
    n%2<2
    n%2<=1
    n%2 $in closed_range(0,1)
    expand: n%2 $in closed_range(0,1)

claim:
    ? forall n N:
        n%2=1
        =>:
            n>=1
            n-1 $in N
    n $in Z
    n>=0
    by contra:
        ? n!=0
        n=0
        n%2=0%2=0
        impossible n%2=1
    n>0
    n>=1
    n-1 $in Z
    n-1>=0
    n-1 $in N

have fn adjacent_pair_swap(n N) N by cases:
    case n%2=0: n+1
    case n%2=1: n-1

claim:
    ? forall n N:
        adjacent_pair_swap(adjacent_pair_swap(n))=n
    n $in Z
    by cases:
        ? adjacent_pair_swap(adjacent_pair_swap(n))=n
        case n%2=0:
            adjacent_pair_swap(n)=n+1
            n+1 $in N
            (n+1)%2=(n%2+1)%2=(0+1)%2=1
            adjacent_pair_swap(n+1)=(n+1)-1=n
            adjacent_pair_swap(adjacent_pair_swap(n))=adjacent_pair_swap(n+1)=n
        case n%2=1:
            n>=1
            n-1 $in N
            adjacent_pair_swap(n)=n-1
            (n-1)%2=(n%2-1)%2=(1-1)%2=0
            adjacent_pair_swap(n-1)=(n-1)+1=n
            adjacent_pair_swap(adjacent_pair_swap(n))=adjacent_pair_swap(n-1)=n

claim:
    ? $bijective(N,N,adjacent_pair_swap)
    claim:
        ? forall x,y N:
            adjacent_pair_swap(x)=adjacent_pair_swap(y)
            =>:
                x=y
        x=adjacent_pair_swap(adjacent_pair_swap(x))=adjacent_pair_swap(adjacent_pair_swap(y))=y
    by def $injective(N,N,adjacent_pair_swap)
    claim:
        ? forall y N:
            exist x N st {y=adjacent_pair_swap(x)}
        adjacent_pair_swap(y) $in N
        adjacent_pair_swap(adjacent_pair_swap(y))=y
        witness exist x N st {y=adjacent_pair_swap(x)} from adjacent_pair_swap(y)
    by def $surjective(N,N,adjacent_pair_swap)
    by def $bijective(N,N,adjacent_pair_swap)

release thm nn::zero_start_real_geometric_series_sum(1/2)

release thm nn::zero_start_real_geometric_series_absolutely_converges(1/2)

claim:
    ? $ts::has_real_tail_series_sum(0,\nn::real_geometric_tail_from_zero<1/2>,2)
    1/(1-1/2)=2
    $ts::has_real_tail_series_sum(0,\nn::real_geometric_tail_from_zero<1/2>,1/(1-1/2))

claim:
    ? forall n {j Z:j>=0}:
        \nn::real_geometric_tail_from_zero<1/2>(n)>=0
    n $in Z
    n>=0
    n $in N
    \nn::real_geometric_tail_from_zero<1/2>(n)=(1/2)^n>0

release thm rr::nonnegative_zero_start_series_rearrangement_candidate(\nn::real_geometric_tail_from_zero<1/2>,adjacent_pair_swap,2)

release thm rr::nonnegative_zero_start_series_rearrangement_has_same_sum(\nn::real_geometric_tail_from_zero<1/2>,adjacent_pair_swap)

release thm ts::real_tail_series_sum_implies_convergent(0,\rr::zero_start_real_index_composition<\nn::real_geometric_tail_from_zero<1/2>,adjacent_pair_swap>,2)

release thm ts::real_tail_series_sum_value(0,\rr::zero_start_real_index_composition<\nn::real_geometric_tail_from_zero<1/2>,adjacent_pair_swap>,2)

\ts::real_tail_series_sum<0>(\rr::zero_start_real_index_composition<\nn::real_geometric_tail_from_zero<1/2>,adjacent_pair_swap>)=2

claim:
    ? \rr::zero_start_real_index_composition<\nn::real_geometric_tail_from_zero<1/2>,adjacent_pair_swap>(0)=1/2 and \rr::zero_start_real_index_composition<\nn::real_geometric_tail_from_zero<1/2>,adjacent_pair_swap>(1)=1 and \rr::zero_start_real_index_composition<\nn::real_geometric_tail_from_zero<1/2>,adjacent_pair_swap>(2)=1/8 and \rr::zero_start_real_index_composition<\nn::real_geometric_tail_from_zero<1/2>,adjacent_pair_swap>(3)=1/4
    adjacent_pair_swap(0)=1
    adjacent_pair_swap(1)=0
    adjacent_pair_swap(2)=3
    adjacent_pair_swap(3)=2
    \rr::zero_start_real_index_composition<\nn::real_geometric_tail_from_zero<1/2>,adjacent_pair_swap>(0)=\nn::real_geometric_tail_from_zero<1/2>(1)=(1/2)^1=1/2
    \rr::zero_start_real_index_composition<\nn::real_geometric_tail_from_zero<1/2>,adjacent_pair_swap>(1)=\nn::real_geometric_tail_from_zero<1/2>(0)=(1/2)^0=1
    \rr::zero_start_real_index_composition<\nn::real_geometric_tail_from_zero<1/2>,adjacent_pair_swap>(2)=\nn::real_geometric_tail_from_zero<1/2>(3)=(1/2)^3=1/8
    \rr::zero_start_real_index_composition<\nn::real_geometric_tail_from_zero<1/2>,adjacent_pair_swap>(3)=\nn::real_geometric_tail_from_zero<1/2>(2)=(1/2)^2=1/4

release thm nn::zero_start_real_geometric_series_sum(-1/2)

release thm nn::zero_start_real_geometric_series_absolutely_converges(-1/2)

claim:
    ? $ts::has_real_tail_series_sum(0,\nn::real_geometric_tail_from_zero<-1/2>,2/3)
    1/(1-(-1/2))=2/3
    $ts::has_real_tail_series_sum(0,\nn::real_geometric_tail_from_zero<-1/2>,1/(1-(-1/2)))

release thm rr::absolutely_convergent_zero_start_series_rearrangement_converges_absolutely(\nn::real_geometric_tail_from_zero<-1/2>,adjacent_pair_swap)

release thm rr::absolutely_convergent_zero_start_series_rearrangement_candidate(\nn::real_geometric_tail_from_zero<-1/2>,adjacent_pair_swap,2/3)

release thm rr::absolutely_convergent_zero_start_series_rearrangement_has_same_sum(\nn::real_geometric_tail_from_zero<-1/2>,adjacent_pair_swap)

release thm ts::real_tail_series_sum_value(0,\rr::zero_start_real_index_composition<\nn::real_geometric_tail_from_zero<-1/2>,adjacent_pair_swap>,2/3)

\ts::real_tail_series_sum<0>(\rr::zero_start_real_index_composition<\nn::real_geometric_tail_from_zero<-1/2>,adjacent_pair_swap>)=2/3
```
