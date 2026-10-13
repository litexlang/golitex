# Mathematical interfaces and dependencies

The [manifest](litex.config) exposes the selected chapter development in
source order: `Introduction`, `chap1` through `chap7`, `appendix_a`, then
`chap8`. [README.md](README.md) supplies the reading path and [STATUS.md](STATUS.md)
the omissions and foundation assumptions. The original number carriers are
Litex builtins; chapter constructions explain and connect their interfaces.

## Induction, sets and arithmetic

Chapter 2 uses `by induc` with a base and successor step. Chapter 3 develops
map predicates such as `chap3::is_injective_fn(S, T, f)` and equal cardinality
through bijections. The function type `fn(x S) T` fixes source and target;
an injectivity predicate supplies a property of that function, not its
existence. Later countability proofs reuse this distinction.

Chapter 4 introduces formal differences and rational distance. Chapter 5
uses rational Cauchy representatives to connect its construction vocabulary
to builtin `R`. Representative existence and real completeness remain
explicit axioms. They must not be read as consequences of merely declaring
a predicate or naming a real value.

## Roots and powers

`chap5::zero_positive_fractional_power(n)` applies for `n N+` with the
positive-exponent premise `1/n $in R+`. Its conclusion is `0^(1/n)=0`.
The builtin zero-power rule supplies this case; exponent zero or a negative
exponent is outside the theorem. Nonnegative roots and positive-base power
continuity are separate results with separate domains.

## Limits and series

`chap6::is_tail_close_to(a, L, epsilon, n0)` bounds every later term's distance
from `L`; `has_eventual_closeness_to` introduces the tail witness, and
`has_limit` quantifies over positive epsilon. The sequence carrier is
`seq(R)`, indexed by `N+`. A convergence predicate does not choose a limit
for arbitrary sequences. Existence and uniqueness support later limit
interfaces under their declared convergence conditions.

Chapter 7 depends on these predicates. Its partial-sum sequences turn series
questions into limit questions. Harmonic divergence uses dyadic lower bounds;
alternating convergence uses paired tail estimates; condensation compares
partial sums; absolute-convergence rearrangement bounds use a bounded prefix.
These proofs are distinct from the omitted Riemann rearrangement construction
for conditionally convergent series. Set-indexed summation is also omitted.

## Countability, products and choice

`chap8::embeds_into(S, T)` asks for an injective function using Chapter 3's
predicate. `chap8::is_at_most_countable(X)` specializes the target to `N`.
It does not assert that every set embeds into `N`; a caller must establish the
witness and injectivity. The countable-union proof encodes an element through
an owner index and a fiber code, using the retained choice background.

The independent Cantor power-set argument is included; the decimal proof of
real uncountability is omitted. Product representations distinguish supplied
coordinate functions from their existence. The two explicit choice axioms
and abstract `choice_property` remain visible in Chapter 8. Appendix A is an
ordered prerequisite, not an additional claim of book-wide coverage.

## Historical small examples

`naturals.lit`, `maps.lit` and `finite_products.lit` remain as earlier short
examples. They are not exports of the current chapter manifest. Their separate
strict receipt records their previous context and public limit dependency;
do not combine that receipt with the non-strict chapter gate.
