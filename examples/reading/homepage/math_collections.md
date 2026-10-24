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

## Branch chapter: linear algebra to unique standard coordinates

Keep the complete lecture prefix through section2.4: real field and plane,
subspaces with an affine-line counterexample, finite partial sums, span,
independence and bases. Standard expansion supplies existence; the theorem
`standard_coordinates_unique` compares coordinates to prove uniqueness for
the standard basis of the real plane. It does not claim the later general
dimension theorem or rank-nullity material.

## Branch chapter: open sets to homeomorphisms

Keep Chapters1–2, including every foundational definition and proof. Discrete
and indiscrete topologies on `{0,1}` contrast continuity of the two identity
directions. Preimages provide continuity of composition and the closed-set
criterion; the self-inverse swap closes the chapter with a homeomorphism.
Later connectedness, compactness and real-line IVT material is not included.

## Branch chapter: finite probability to Bayes

Keep the complete two-point probability, expectation and variance source.
The least-squares decomposition links it to the first short example.
`bayes_rule` substitutes `joint = likelihood * prior` in conditional
probability with positive evidence; its concrete coherent input yields1/2.
The weighted affine-expectation identity is algebraic and needs no probability
vector premise. No general probability-space or measure construction is claimed.

## Branch chapter: a complete geometry problem

Keep IMO1966P6's complete definitions and proof. Strict interior points on
the three sides give affine witnesses; determinant factorizations express
corner triangle area ratios. A case split forces one ratio to be at most1/4.
The conclusion `16 * small_det^2 <= original_det^2` compares unsigned areas
without introducing square roots. Nondegeneracy and strict interior domains
remain explicit. The source's theorem name `problem_12` is its collection ID,
not the official IMO problem number.

The seven branch chapters reuse existing showcase source (complete files or
complete prefixes), with Chinese reading introductions. The number-theory
chapter also uses inline bodyless `by def`. Exact source ranges, file hashes
and verification records live in `long_examples.json`.

The strict main collection uses existing kernel interfaces with no user trust
or axioms. Separate homepage language demonstrations retain their explicitly
marked assumptions; they are outside that strict collection.

## Complete homepage snapshot

Fifty distinct strict homepage/shared-public examples now join the seven branch
chapters. Full orthogonal projection uses a nonzero direction in `cart(R,R)`,
proves positivity of its squared norm before division, then orthogonality,
squared-distance decomposition, minimality and uniqueness. This is the actual
homepage proof, including the concrete projection of (3,1) onto (1,1).

The ellipse example retains `a > b > 0` and `c > 0`; its checked result is the
squared horizontal separation of its designated focal points, not a new proof
of an arbitrary geometric characterization of ellipses. The group example
retains its complete GroupProperty and Group declarations before cancellation.
Newton residual identities are exact finite-step identities, not a general
convergence theorem. Age arithmetic and all small language examples remain
standalone sources. Exact source identities, normalization and checks are in
`homepage_sources.json`; human-readable entries are in `homepage_examples.md`.

Two explicit-assumption examples and four intended domain failures are stored
separately. They must not be promoted into the strict mathematical collection
or have their assumptions/failed checks hidden. The multi-file Newton example
retains both source files and its original configuration in `reuse/`.

## Independent problem/correction exercises

The reading gallery includes four separate expected-failure exercises under
`problems/`, each with a checked correction. Names must be declared before use;
reflexivity does not legalize division by zero; the real square root requires
a nonnegative input. The Socrates pair uses abstract predicate interfaces
`is_human(person)` and `is_mortal(person)`, with a nonempty discussion universe.
Its rejected conditional lacks the human antecedent; the corrected conditional
provides that premise before applying the universal mortality rule. No user
axiom or trust is added. A missing proof is not an established negation.
The gallery owns links between independent exports; failed examples never
enter the main ordered module or share execution/fact identities with it.
