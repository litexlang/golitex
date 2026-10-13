# Sequences, limits and series

This lecture is a client of the public Tao chapter module. Named functions
are opened with `release obj def` before their callable interfaces are used.
Its manifest mounts
that module as `Tao`; its single export is `analysis`. It defines no competing
limit or series predicates. It presents one explicit epsilon proof and cites
the chapter results for the subsequent examples. The source follows
one route: a concrete tail estimate, convergence, uniqueness, limit arithmetic,
geometric sequences, then a geometric series.

## Epsilon tails and convergence

`Tao::chap6::is_tail_close_to(a, L, epsilon, n0)` quantifies over every positive
index at least `n0`. `has_limit(a, L)` requires such a cutoff for every positive
epsilon. The concrete example uses the canonical `reciprocal_nat_seq` and
`reciprocal_nat_order_reversing(11, n)` to establish a tail for error `1/10`.
This single tail bound is not a proof for every epsilon. The lecture then
supplies the full epsilon proof using Chapter 5's
`archimedean_property(epsilon)` to select a cutoff and Chapter 6's reciprocal
order theorem to control every later term. Anonymous ambient chapter facts
are not automatically merged into a caller.

## Uniqueness and arithmetic

`sequence_limit_unique(a, L1, L2)` requires two limit facts for the same
sequence. The lecture uses it to show that any limit of the reciprocal sequence
is zero. `constant_sequence_has_limit(3)` supplies the second sequence for
`seq_add_converges_to(a, b, x, y)`. That theorem gives limit `x+y` to the
pointwise sum after both input convergence facts have been established.

## Geometric sequences and sums

`geometric_positive_lt_one_converges_to_zero` treats positive ratios below one.
`geometric_abs_lt_one_converges_to_zero` also permits negative ratios of
absolute value below one. `geometric_minus_one_diverges` demonstrates the
boundary at ratio -1; boundedness alone is insufficient for convergence.

`Tao::chap7::geometric_series_formula(x)` uses terms `x^(n-1)`, indexed by
`N+`, so its first term is 1. Under `abs(x)<1` and `1-x!=0`, the sum is
`1/(1-x)`. The lecture specializes `x=1/2`, giving 2. The convergence of terms
and the convergence of partial sums are different assertions.

## Foundation and verification boundary

The lecture introduces no new axioms, abstract predicates or direct trust.
Mounting the current companion module includes its selected Chapters 1–8 and
Appendix A, with their explicit assumptions. Even though the lecture cites
only Chapters 6 and 7, the imported module's complete export selection is the
verified dependency scope. Consult [verification.json](verification.json)
and the companion [STATUS.md](../analysis/STATUS.md). No whole-book or Lean
acceptance follows from this lecture.
