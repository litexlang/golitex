# Mathematical reading design

This project reuses checked homepage developments as reading material. It
introduces no new native mathematical capability. Definitions, complete
proofs and numerical applications remain together in their source files.

## Least-squares center

`is_least_squares_center(center, a, b, c R)` means that every real candidate
has squared error at least as large as the center's. The quantifier is part
of the definition; an inequality for one candidate cannot replace it.
`mean(a, b, c)` is the real-valued function `(a + b + c) / 3`. The proof uses
the squared-error decomposition and nonnegativity of a square. Its numerical
application compares center 84 and candidate 80 for 72, 84, 96. The definition
and instantiated inferred universal condition are the main reading tracer.

## Sets

Use the builtin `union`, `intersect` and membership interfaces directly.
Union commutativity is a universal fact; particular membership and
nonmembership facts provide concrete applications. No wrapper predicate is
needed. A union member need not be an intersection member.

## Newton error

`newton(x R+) R = (x + 2 / x) / 2` requires a positive input, so its
denominator is nonzero. With `r = sqrt(2)`, expansion gives
`newton(x) - r = (x - r)^2 / (2 * x)`. This is an exact one-step identity;
it is not a convergence proof for an arbitrary initial point. The reader can
show the domain, equation, codomain and checked calculation separately.

## Irrationality of √2

The target is `not sqrt(2) $in Q`. The contradiction assumes a rational
value, uses the builtin reduced-fraction theorem and prime-divisibility of
powers, and derives `2 <= gcd(p, q) = 1`. Numerator `p Z` and positive
denominator `q N+` and the coprimality condition are essential. Local
contradiction hypotheses must remain distinguishable from global facts.

## Cantor's theorem

For any set `S` and function `f fn(x S) power_set(S)`, the theorem asserts
`not $surjective(S, power_set(S), f)`. The diagonal subset is an actual
subset of `S`; a hypothetical preimage contradicts its membership condition.
The argument preserves both the function's domain/codomain and the local
surjectivity assumption. It does not assume that `S` is finite or nonempty.

## Longer lecture: divisibility to Diophantine equations

Reuse the existing number-theory showcase's witness-facing `divides_by`,
`is_gcd_certificate`, `linear_diophantine_soluble` and `congruent_mod` interfaces.
The supplied positive gcd certificate includes divisor laws and a Bezout
witness; it does not define a new global gcd function. The proof chain leads
to the concrete solution `84*(-3) + 30*9 = 18`. Preserve integer domains,
positive modulus and all witness scopes. General Euclidean algorithms and CRT
are outside this lecture.

## Longer lecture: epsilon tails and unique limits

Reuse the existing real-analysis showcase, keeping sequences on `N+`.
Tail closeness leads to a limit predicate and convergence. A constant-sequence
template supplies an example; a common tail index and triangle inequality
prove uniqueness. Only convergent sequences may enter `sequence_limit_value`.
This is an explicit pedagogical definition, not a replacement for native limit
interfaces; no uniform-convergence or integration theorem is added.

## Longer lecture: integer groups to kernels

Reuse the abstract-algebra lecture's `Group<A nonempty_set>` structure,
integer additive example, subgroup predicates, homomorphisms and kernel sets.
Associativity, identity and inverse laws are structure conditions; cancellation
and preservation of identity/inverse are proved consequences. The kernel is a
subset, not a predicate or arbitrary record. Its normality and the equivalence
between trivial kernel and injectivity culminate in doubling and zero-map
examples. Quotient groups and Lagrange's theorem are outside this slice.

The three longer files retain all mathematical source from their maintained
showcases, adding only introductory reading comments. Provenance, exact file
hashes and current verification are recorded in `long_examples.json`.

All eight developments use existing kernel interfaces. They have no user
trust, axioms, abstract predicate placeholders or unresolved proof holes.
