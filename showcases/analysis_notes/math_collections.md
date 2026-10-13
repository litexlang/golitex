# Sequences, limits and infinite sums

This module exports one self-contained `analysis.lit`. Its manifest has no
imports. Mathematical definitions, auxiliary estimates and proofs all live in
that file. The source follows one path: a concrete tail estimate, reciprocal
convergence, uniqueness, limit arithmetic, geometric decay, and partial sums.

## Epsilon tails and convergence

`is_tail_close_to(a, L, epsilon, start)` bounds every positive index at least
`start`. `has_eventual_closeness_to` asks for such an index; `has_limit` asks
for one for every positive epsilon. Sequences have carrier `seq(R)`, indexed
by `N+`. A single fixed-error estimate is insufficient for convergence.

`reciprocal(n)=1/n` is defined only on positive natural numbers. The local
`reciprocal_decreases` proof compares two fractions with a common positive
denominator. Builtin Archimedean mathematics supplies an index with
`1/start<epsilon`; the lecture constructs the tail witness and checks the
limit definition. It introduces no completeness or representative axioms.

## Uniqueness and arithmetic

`sequence_limit_unique(a, L1, L2)` compares two tails at a common index and
uses the triangle inequality. It proves uniqueness of the limiting value,
not uniqueness of a cutoff. `constant_sequence_has_limit` checks distance
zero, while `seq_add_converges_to` allocates half the error to each sequence.
Both theorems are proved locally before their applications.

## Geometric decay and a counterexample

`powers_of_two_grow` proves `2^n>=n+1` by induction. Another induction proves
`(1/2)^n*2^n=1`. These facts give `0<=half_power(n)<=1/n`.
`dominated_by_reciprocal_converges` then supplies a local comparison theorem.
It requires both nonnegativity and the upper bound at every positive index.

`alternating_half_power(n)=(-1/2)^n` uses the proved identity for its absolute
value to transfer the same epsilon estimate. `alternating(n)=(-1)^n` has no
real limit: on any alleged small-error tail, even and odd indices still give
1 and -1. This illustrates why a bounded sequence need not converge.

## Partial sums and a particular series

`geometric_partial_sum` is defined recursively on `N`, with initial value
zero and the next term added at each step. Its terms are `1,1/2,1/4,...`.
`geometric_partial_sum_formula` proves `S_n=2-2*(1/2)^n` by induction. The
final argument constructs an epsilon tail for the positive-index sequence
of partial sums and proves its limit is 2.

This is a direct development of one infinite sum. There is no general
`has_series_sum` interface, no arbitrary-ratio geometric-series theorem,
and no claim that terms tending to zero suffice for series convergence.

## Verification boundary

The file has no external module references or user assumptions. Strict
registered and config-free checks are recorded in
[verification.json](verification.json). The builtin real and natural number
systems, arithmetic, Archimedean property and verifier are the background.
There is no construction of the real numbers from first principles, whole-book
coverage, Lean replay or independent kernel soundness audit.
