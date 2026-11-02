# Real sequences on integer tails

Real values retain native R. A sequence beginning at start Z has the actual
domain {j Z:j>=start}. The source predicates use closed epsilon bounds and
positive real radii. Both Cauchy and limit predicates are proved equivalent
to the native strict-epsilon relations on the actual N+ reindex a(start+k-1).

```ini
[import std]
RealSequences = real_sequences
[alias]
rs = RealSequences::main
[export]
main = "./main.lit"
```

`real_tail_positive_index(start,k)` supplies membership of start+k-1 in the
original tail. Cite it before forming an original-value goal at that index;
`real_tail_original_index` gives the inverse n-start+1 in N+.

The eight laws of Tao Analysis I 6.1.19 use actual pointwise sum, product,
scaling, difference, reciprocal, quotient, maximum and minimum templates.
Reciprocal and quotient denominators have the complete original tail domain
and codomain R*, and their limits must be nonzero. No zero-valued fallback
or deleted index is introduced. If an existing R-valued denominator is known
pointwise nonzero, first prove b(n) in R* at each original index, then construct
the actual same-value function with R* codomain. Independent full-domain proofs
of both source forms follow this route; no function is retagged by assumption.

The partial selected value is `\rs::real_tail_limit<start>(a)`; prove
`$rs::is_convergent_real_tail(start,a)` before using it. Native lim(a)
continues to take exactly one N+ real sequence. Bounded-by parameters are
nonnegative real numbers, including zero; boundedness has a positive witness.

This complete example starts at a negative integer and takes max with a
negative constant before selecting its limit:

```litex
release thm rs::positive_real_reciprocal_tail_limit
release thm rs::real_tail_constant_limit(-3,-2)
release thm rs::real_tail_constant_limit(-3,0)
release thm rs::real_tail_maximum_limit(-3,\rs::real_tail_constant<-3,-2>,\rs::real_tail_constant<-3,0>,-2,0)
$rs::has_real_tail_limit(-3,\rs::real_tail_maximum<-3,\rs::real_tail_constant<-3,-2>,\rs::real_tail_constant<-3,0>>,0)
release thm rs::real_tail_limit_implies_convergent(-3,\rs::real_tail_maximum<-3,\rs::real_tail_constant<-3,-2>,\rs::real_tail_constant<-3,0>>,0)
release thm rs::real_tail_limit_value(-3,\rs::real_tail_maximum<-3,\rs::real_tail_constant<-3,-2>,\rs::real_tail_constant<-3,0>>,0)
\rs::real_tail_limit<-3>(\rs::real_tail_maximum<-3,\rs::real_tail_constant<-3,-2>,\rs::real_tail_constant<-3,0>>)=0
```

All mathematical results are checked source proofs over native scalar
arithmetic and sequence facts. There are no new axioms, trust declarations,
number models, kernel/WD changes or infinity-valued limit conventions.
Source-order correspondence, complete imported contracts, actual negative-start
reciprocal tracer and false/domain controls remain under experiments/.
