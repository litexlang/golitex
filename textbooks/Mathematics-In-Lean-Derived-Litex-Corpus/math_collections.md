# MIL-derived Litex mathematical interface map

This is the design manual for the independent Litex translation pressure-test
corpus in this directory. It records the mathematical nodes that organize the
executable chapters; it is not an alternative edition of *Mathematics in Lean*
or a reconstruction of Mathlib's architecture.

Source snapshot: *Mathematics in Lean* at
`6dfa2c166a410d2f0f278d327ea81ae0fa6d3c32`.

“Checked” means checked by the current Litex verifier in this project. It does
not mean Lean-certified, and it does not imply that omitted source results have
been proved. All executable corpus files are free of `trust`, `know`, `axiom`,
and `abstract_prop`. Source mathematics that is not yet implemented is listed in
the comment-only `todo.lit`. The project imports no Litex standard-library
module and has no cite module. Its kernel builtin rules remain part of the
verifier boundary, so this source-level independence is not a claim that the
development is independent of the Litex implementation.

## Closed facts and reusable relationships

A closed source theorem should remain a direct fact or named `thm`. A `prop`
is reserved for a relationship that later declarations apply to candidates.
For example:

```litex
prop is_even_fn(f fn(x R) R):
    forall x R:
        f(-x) = f(x)
```

The nearest rejected form is a zero-argument proposition used only to wrap one
closed theorem. This distinction keeps later hypotheses readable and prevents
an unproved theorem from masquerading as a definition. It affects every
chapter: algebraic structure laws, convergence, continuity, differentiability,
and measurability are reusable relationships; a source identity or existence
result is a fact and remains executable only when checked.

Fermat's Last Theorem illustrates the boundary. The source item is not
implemented here, so neither a theorem nor a wrapper proposition appears in
Chapter 1. Its exact mathematical obligation is recorded in `todo.lit`.

## Carrier-first algebra

Groups, rings, fields, modules, and vector spaces are modeled by an explicit
carrier plus explicit operations:

```litex
prop is_monoid(G set, mul fn(x, y G) G, one G)
prop is_commutative_ring(Ring set, add fn(x, y Ring) Ring, zero Ring,
    neg fn(x Ring) Ring, mul fn(x, y Ring) Ring, one Ring)
```

The rejected form is to specialize a generic source theorem to ordinary real
or integer arithmetic merely because the verifier can normalize it. These
interfaces feed homomorphisms, subobjects, actions, ideals, and linear algebra.
Elementary projections and short closure arguments are checked. Group
normalization, finite-group theory, selected inverses, and larger structure
assemblies remain deferred where their supporting proof chain is absent.

Chapter 2 deliberately presents the same additive-commutative-group content in
two forms. `is_additive_commutative_group(A, add, zero, neg)` is a predicate on
operations supplied by the caller, matching the source-facing proof lesson.
`AdditiveCommutativeGroup<s>` is the bundled alternative: one value contains
the operations and their law block, and
`additive_commutative_group_add_neg_cancel` accesses them through projections.
The nearest rejected design is replacing every Chapter 2 theorem with the
struct form; that would hide the explicit parameters which the chapter is
teaching. The struct requires a nonempty carrier because it stores `zero`.

Chapter 8's ordinary integer ring is a checked `Ring<Z>` object whose fields
are integer addition, zero, negation, multiplication, and one. This preserves
the source instance as usable callable data; the rejected form is a proposition
merely asserting that the integers form a ring. The separate generic theorem
deriving additive commutativity from the weaker ring axioms remains deferred.

The integer natural-scalar instance is likewise an actual
`AdditiveMonoidWithNSmul<Z>` object. Its action is `(n,x) |-> n*x`, so the zero
and successor laws normalize directly. The generic recursive natural-scalar
selection and the componentwise product instance remain separate deferred
interfaces; they are not prerequisites for this concrete object.

## Source-local elementary number theory

The elementary number-theory vocabulary used across the early chapters is
defined inside this project rather than imported. Chapter 2 defines integer
divisibility by an explicit witness and defines gcd as the maximum of the
finite nonempty set of positive common divisors. Finiteness is proved in place:
the common-divisor set is bounded by a finite interval and is recovered as a
double relative complement. The gcd positivity, divisibility, greatestness,
base, and symmetry laws are ordinary checked theorems built on that definition.

Chapter 4 defines primality directly on `N_pos`. Chapter 5 introduces
`integer_quotient` as a callable function with `have fn ... by exist!`; the
kernel discharges only the narrow unique-existence fact for Euclidean division.
This division of responsibility is intentional: the mathematical vocabulary
and reusable proof route remain visible Litex, while arithmetic, remainder,
finite-set difference, finite extrema, and Euclidean-quotient existence are
explicit builtin boundaries. The rejected form is an empty cite package or an
imported theorem whose simple local proof is hidden from the corpus reader.

## Functions, bounds, relations, and convergence

Chapters 3 and 4 distinguish functions from their graphs and properties.
Bounds and convergence are parameterized relationships; images and inverse
images are set-valued constructions with explicit witnesses. Generic order is
represented by a binary relation carrier rather than a proposition-valued
return type.

The sequence carrier is `N`, including zero. Replacing it by `N_pos` was
rejected because it changes the source domain. Epsilon-N and epsilon-delta
definitions are kept even when their major analytic consequences are deferred,
because these definitions are useful downstream and have independent
mathematical content.

Lean's truncated natural predecessor is represented by the callable function
`natural_predecessor : N -> N`, with a zero branch and the ordinary `n - 1`
branch for positive naturals. This keeps the source domain and makes the
factorial power bound well-typed at zero. The rejected form is to reuse
ordinary integer subtraction at zero, where `0 - 1` is `-1` rather than a
natural exponent. The piecewise function and the factorial power bound are
checked; no existence or well-definedness hole remains in this local
interface.

Arbitrary choice is not smuggled into a function declaration. The source's
total inverse-with-default and the recursive Schroeder-Bernstein construction
remain in `todo.lit`; injective and surjective relationships that do not require
that choice remain implemented.

## Finite and inductive mathematics

Finite sets use the installed finite-set carrier, size, finite unions, and
explicit indexing. Chapter 6 keeps finite counting objects and specification
relationships for lists, trees, and propositional formulas.

The finite triangle is a callable subset of its exact Cartesian ambient
carrier:

```litex
have fn triangle(n N) power_set(cart(range(0, n + 1), range(0, n + 1)))
```

It is represented by deleting pairs whose first coordinate is at least their
second. This makes finiteness follow from the finite Cartesian square and
finite-set difference. The rejected form is an untyped subset plus a trusted
subset-finiteness bridge. Its cardinality formula remains separate source debt
in `todo.lit`.

The rejected shortcut is to identify a new source inductive carrier such as
`MyNat`, `BinTree`, or `PropForm` with an existing carrier. A real implementation
must supply its constructors, induction/recursion interface, recursive
functions, and defining equations. Chapter 6 can nevertheless prove
`list_append_nil` and `list_map_map` for every callable candidate satisfying
the checked recursion specifications. Its piecewise updated Boolean valuation
is also a callable template. The missing canonical list selections and the
larger `BinTree` and `PropForm` recursion families remain in `todo.lit`.

The indexed standard simplex is the set of real coordinate functions on
`range(0, n)` whose coordinates are nonnegative and whose finite sum is one.
Its midpoint is therefore a callable pointwise construction:

```litex
template<n N>:
    have fn standard_simplex_midpoint(a, b \standard_simplex<n>) fn(i range(0, n)) R
```

The corresponding closure theorem is checked by coordinate nonnegativity and
finite-sum linearity. The nearest rejected form is a proposition merely saying
that some midpoint exists, because later consumers must evaluate the resulting
coordinate function.

## Equivalences, subobjects, and quotients

An equivalence is callable forward and inverse data with two inverse laws.
Submonoids, subgroups, subspaces, subrings, and ideals are subsets with closure
laws. Intersections are literal set intersections when possible, which keeps
the proof close to the mathematical argument.

A checked submonoid carrier now inherits an actual `Monoid<carrier>` object by
restricting ambient multiplication and identity. The exact tuple is first
proved to satisfy the monoid structure; only then does a template expose the
callable inherited object. The nearest rejected form is a proposition saying
that an inherited monoid exists without supplying its operations.

Quotient work is intentionally layered:

1. define the equivalence relation or coset;
2. define the quotient carrier;
3. prove representative independence;
4. only then expose quotient operations and universal lifts.

The current chapters implement several relations, cosets, and quotient
carriers, but do not postulate steps 3 and 4. The rejected form is an opaque
selected multiplication or lift whose well-definedness is hidden. Normality,
ideal membership, or kernel containment must be visible in any future
implementation. Quotient monoids, quotient groups/rings/spaces, first
isomorphism theorems, and CRT therefore remain explicit todo families.

## Gaussian integers and polynomial carriers

Gaussian integers are coordinate pairs with direct addition, multiplication,
conjugation, norm, and rank functions. Projection, norm-zero, positivity,
multiplicativity, conjugation, and the checked rank inequality form a usable
core. The Euclidean-domain construction still depends on centered division and
a strict remainder-norm proof, so it is deferred rather than represented by a
trusted structure object.

Polynomials are finite-support coefficient functions. This is the right
carrier because coefficient lookup is direct and later arithmetic can be
defined through finite sums. The nearest rejected form is an opaque polynomial
multiplication or evaluation function with no finite-sum construction. X,
constants, multiplication, composition, evaluation, roots, and degree theory
remain in `todo.lit` until those constructions exist.

## Linear algebra

Chapter 10 builds from fields, vector spaces, and linear maps to binary product
and coproduct maps, subspaces, span, kernels, ranges, quotient carriers,
eigen-data, concrete matrices, and basis relationships. Linear-map composition
and the span universal property follow their short natural proofs and are
checked.

The callable product, coproduct, identity, and countable-set templates are the
implemented interfaces. Strict verification now unfolds their applications
when carrier parameters remain symbolic; the focused C10 reproduction verifies
this behavior directly. Some C10-C13 pointwise facts retain an explicit lambda
or set-builder form because it exposes the coordinate or membership
calculation, not as a workaround for a live `kernel_problem`.

Dependent direct sums, quotient operations, endomorphism polynomials, basis
coordinates, finite indexed matrix sums, and dimensions require additional
objects. Their ideal forms are callable functions or selected values justified
by existence and uniqueness; turning them into propositions was rejected. The
finite-dimensional interface remains an existence relationship for a finite
basis, which supports later hypotheses without claiming a selected dimension.

## Filters, metrics, and topologies

Filters and topologies are families of subsets with closure laws. Metric and
topological convergence, continuity, compactness, completeness, density, and
separation are relationships on explicit carriers. Real-distance laws, ball
center membership, topology axioms, limit and continuous-map composition,
eventual conjunction and implication, preservation of real limits under
eventual equality, the open-preimage continuity equivalence, the forward
pairwise-to-anchored Cauchy bridge, and the direct convergence consequence of
completeness are checked.

The checked `topologically_continuous_composition` theorem is ordinary
composition between three fixed topologies. The retained source item instead
asks for an iff after replacing the middle topology by the topology coinduced
along the first map. That topology-changing composition equivalence remains
explicit source debt in `todo.lit`; ordinary composition does not discharge
it.

This definition-first layer is retained because it gives later theorems the
right hypotheses. The rejected form is to add a large collection of theorem-
shaped propositions at the top of the chapter. Filter algebra, the closure
characterization theorems, the reverse Cauchy bridge, other compactness and
completeness theorems, Baire, separation results, extensions, and sequential compactness
remain in `todo.lit` until their actual proof spines are formalized.

The C11 pressure test exposed a kernel bug in which automatic universal-fact
matching replaced a non-quantified free set parameter. The matcher now treats
only the fact's own quantified header as instantiable and keeps captured outer
parameters rigid. Eventuality and limit proofs still call small projection
theorems with every set and filter argument explicit because that interface is
mathematically clear; the former counterexample is retained as a rejecting
kernel regression rather than live proof debt.

## Differential calculus

A derivative is first a relationship between a function, a point, and a
candidate linear value or map:

```litex
prop has_derivative_at(f fn(x R) R, x0, L R)
prop has_frechet_derivative_at(E, F set, ..., f fn(x E) F,
    fprime fn(x E) F, x0 E)
```

This representation supports honest hypotheses without selecting a derivative.
A total `deriv`, `fderiv`, or local inverse should be exposed only after the
needed uniqueness or existence theorem. The rejected form is an arbitrary
callable selector whose characteristic laws are themselves deferred.

Normed-space, Cauchy/completeness, continuous-linear-map, asymptotic, Frechet,
strict-Frechet, and continuous-linear-equivalence relationships remain
implemented. The identity map has the direct bound-one proof. Derivative
selection, Rolle/MVT, finite-dimensional completeness, operator norms, higher
derivatives, and the inverse function theorem remain in `todo.lit`.

## Measurable spaces and measure candidates

Chapter 13 keeps sigma-algebras as families of subsets closed under complement
and countable union. Countable intersection is proved by the textbook route:
complement every member, take a countable union, then complement again.

The extended nonnegative reals have not yet been constructed in Litex. Instead
of inventing a false carrier, the checked measure interface exposes the value
carrier, zero, and infinite-sum operation as parameters:

```litex
prop is_measure_on(X, V set, M power_set(power_set(X)), zero V,
    infinite_sum fn(a fn(n N) V) V, mu fn(S power_set(X)) V)
```

This is a genuine countable-additivity interface and supports a direct
disjoint-union theorem. It is not claimed to be Mathlib's ENNReal-valued
measure. The rejected form was a collection of trusted ENNReal, integral,
product-measure, and Jacobian selectors. ENNReal specialization, interval and
Bochner integration, dominated convergence, Fubini, convolution, and change of
variables remain in `todo.lit`.

Almost-everywhere truth is parameterized by the value carrier and its zero and
uses a measurable zero-valued exceptional set. This preserves the semantic
role without depending on an unimplemented integral.

## Checked/deferred ownership

Executable chapter files contain only definitions, constructions, and facts
that the ordered project runner checks. The single `todo.lit` owns all known
unimplemented source mathematics and is intentionally comment-only and absent
from `litex.config` exports.

When a todo family is resumed, first reconstruct its natural-language proof or
construction, then restore the smallest source-facing declaration in source
order and run a representative use probe. Only after the implementation passes
should the matching todo paragraph be removed and its JSONL record changed
from `blocked` to `verified`.
