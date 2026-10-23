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

This is convergence in the given `N+` order. Convergence alone does not imply
absolute or unconditional convergence or permit rearrangement. Empty prefixes, other
carriers, infinite values, products and function series are outside this
module. No new AST node is needed for these definitions.

The implemented names and exact call order are in [README.md](README.md).
