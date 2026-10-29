# Mathematical interfaces for ordered real series

Fix a complete function `a : N+ -> R`. For positive integers `n,m`, define

```text
S_n(a) = sum(1,n,a)
partial_sums(a)(n) = S_n(a)
has_series_sum(a,L) iff has_seq_limit(partial_sums(a),L)
is_convergent_series(a) iff exists L in R, has_series_sum(a,L)
series_tail(a,m)(n) = a(n+m)
```

The partial-sum function and its sequence are constructions. Convergence and
the candidate relation are propositions. Once convergence is proved,
`series_sum(a)=lim(partial_sums(a))` is a guarded selected real value. Native
limit uniqueness proves that two series candidates agree. The candidate
definition never refers to that selected value.

Dependencies run from complete real sequences and finite inclusive sums,
through partial-sum identities and sequence limits, to convergence and
selection. Induction proves finite linearity. Native sequence limit laws then
prove series linearity. The identity
`S_n(series_tail(a,m))=S_(n+m)(a)-S_m(a)` proves both tail directions.
The reverse direction uses an epsilon-N proof that restoring finitely many
terms preserves a sequence limit.

For eventual equality after `m`, the corrected sum is
`L-S_m(a)+S_m(b)`. Equality of tails preserves convergence, while their finite
prefixes account for the difference in values. Finite support follows by
applying the zero-series theorem to a tail. Finally,
`a(n+1)=S_(n+1)(a)-S_n(a)` and restoring the first term prove the necessary
zero-term limit.

The absolute-term construction is `absolute_terms(a)(n)=abs(a(n))`.
Absolute convergence is the convergence of this series. The Cauchy series
property is the Cauchy property of its partial sums. Real sequence
completeness proves the Cauchy equivalence. Positive partial-sum comparison
and monotone bounded convergence prove positive comparison. Applying it to
`abs(a)+a`, bounded by `2*abs(a)`, then subtracting `abs(a)`, proves that
absolute convergence implies convergence.

Bernoulli's inequality and the Archimedean property give geometric decay.
Finite geometric and telescoping identities then give actual candidate sums.
The constant nonzero series contradicts the necessary zero-term limit.
Harmonic blocks from n+1 through 2*n have size at least 1/2, contradicting
the Cauchy criterion. These are nonconvergence proofs, not failed searches.

Uniform tail contraction gives a geometric majorant and the ratio test,
including zero terms. The root construction
`root_terms(a)(n)=abs(a(n))^(1/n)` is a complete nonnegative real sequence.
Natural-power monotonicity and root recovery convert a strict root bound
below 1 into a geometric bound. A finite limsup below 1 supplies this bound.
An ordinary limit is a specialization.

Quotient tests use a supplied complete ratio sequence and require a genuinely
nonzero tail before relating it to the quotient. A finite ratio limsup below
1 gives contraction. A finite ratio liminf above 1 gives growth and contradicts
the zero-term condition. A finite root limsup above 1 gives arbitrarily late
terms of magnitude greater than 1, also contradicting that condition.
No test decides the threshold 1; ratio limsup above 1 alone is insufficient.

The reciprocal-square series is compared after its first term with the
nonnegative telescoping sequence `1/k-1/(k+1)`. For any natural exponent
`p>=2`, `k^p>=k^2` gives comparison with the reciprocal-square series.
These theorems establish convergence, not the numerical sum. They do not
establish the general real-exponent p-series test. The cases p=0 and p=1 are
separately divergent by the existing nonzero-constant and harmonic theorems.

For the alternating test, odd terms begin with `a(1)=u(1)` and even terms
are `-u(2*k)`. The nonincreasing `u` tends to zero. Pairing after the first
two terms yields `b(k)=u(2*k+1)-u(2*k+2)`. These nonnegative paired terms
are bounded by the telescoping difference of odd-indexed values of `u`.
Comparison gives convergence of the paired series and therefore of even
partial sums; the next odd term tends to zero. An explicit parity and
interleaving argument then gives convergence of all partial sums. The convergence
conclusion asserts existence of a finite sum, not its value.
The even sums increase, the odd sums decrease, and their common limit is
between adjacent partial sums. This yields the absolute remainder estimate
`abs(L-S_n)<=u(n+1)` for an actual candidate L; an existing tail
construction supplies the next-term equality inside the proof. The included
alternating harmonic consumer proves convergence and separately proves failure
of absolute convergence.

This is convergence in the given `N+` order. Convergence alone does not imply
absolute or unconditional convergence or permit rearrangement. Empty prefixes, other
carriers, infinite values, products and function series are outside this
module. No new AST node is needed for these definitions.

The implemented names and exact call order are in [README.md](README.md).

## Positive finite limit comparison

A positive finite ratio limit L supplies eventual lower and upper bounds
L/2 and 2L. Combining the cutoff with the supplied positive-denominator tail
allows multiplication by b(k) without reversing order. The upper bound
compares a with 2L*b; the lower bound compares b with (2/L)*a. Existing
scaling and eventual comparison prove the two convergence directions, while
finite prefixes remain unrestricted. The proof establishes convergence, not
a sum formula. A zero limit cannot establish the reverse direction, as the
reciprocal-square and harmonic sequences demonstrate. The source adds no
native operation, reserved theorem, search strategy, trust or axiom.
