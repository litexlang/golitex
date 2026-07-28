# MIL-derived Litex mathematical interface map

This is the design manual for the independent Litex translation pressure-test
corpus in this directory. It records the mathematical nodes that organize the
executable chapters; it is not an alternative edition of *Mathematics in Lean*
or a reconstruction of Mathlib's architecture.

Source snapshot: *Mathematics in Lean* at
`6dfa2c166a410d2f0f278d327ea81ae0fa6d3c32`.

“Checked” means checked by the current Litex verifier in this project. It does
not mean Lean-certified, and it does not imply that omitted source results have
been proved. The two directions between neighborhood continuity and the
open-preimage property currently contain narrow `trust`; no executable
`know`, `axiom`, or `abstract_prop` is present. Other absent source mathematics
is listed in the comment-only `todo.lit`. The project imports no Litex standard-library
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

Chapter 2's canonical reusable interfaces are operation-bearing structures:

```litex
struct AdditiveCommutativeGroup<s nonempty_set>:
    add fn(x, y s) s
    zero s
    neg fn(x s) s

struct Group<s nonempty_set>:
    mul fn(x, y s) s
    one s
    inv fn(x s) s

struct Ring<s nonempty_set>:
    add fn(x, y s) s
    zero s
    neg fn(x s) s
    mul fn(x, y s) s
    one s
```

Structures expose their mathematical operations directly. Their `<=>:` bodies
compose reusable law predicates such as
`is_additive_commutative_group(s,add,zero,neg)` and
`is_ring(s,add,zero,neg,mul,one)`. Thus a caller writes `ring.add`,
`ring.zero`, and `ring.mul`; the user-facing path does not grow with the
inheritance depth. `additive_sub` and `ring_two` are templates derived from
those fields, not additional primitives. The nonempty carrier records the
existence of the stored identity element.

The `is_additive_commutative_group`, `is_group`, and `is_ring` propositions are
candidate-data law relations and the composition layer for structs. They are
not parent objects stored inside larger structures. Theorems may receive a
flat structure when callers need a packaged value, or receive operations plus
the corresponding law prop when this is the reusable lower-level theorem
interface. A temporary view object is not part of the public API.

The rejected forms are (1) specializing generic source theorems to ordinary
real or integer arithmetic merely because the verifier can normalize them, and
(2) treating the temporary `is_*` candidate propositions as the permanent
public API. These interfaces feed later homomorphisms, subobjects, actions,
ideals, and linear algebra. Elementary projections and short closure arguments
are checked; group normalization, finite-group theory, selected inverses, and
larger structure assemblies remain deferred where their proof chain is absent.

Chapter 8's source-local integer ring experiment now constructs Chapter 2's
canonical `Ring<Z>` directly. Its fields are integer addition, zero, negation,
multiplication, and one. The rejected forms are a duplicate canonical `Ring`
declaration and a proposition merely asserting that the integers form a ring.
Chapter 8 retains `TwoSidedGroup` under a distinct name because that source
hierarchy assumes right identity as a primitive law, unlike Chapter 2's
left-facing `Group`.

The integer natural-scalar instance is likewise an actual
`AdditiveMonoidWithNSmul<Z>` object. Its action is `(n,x) |-> n*x`, so the zero
and successor laws normalize directly. The generic recursive natural-scalar
selection and the componentwise product instance remain separate deferred
interfaces; they are not prerequisites for this concrete object.

Chapter 8's `Module<Scalar,M>` follows the same flat-data rule. It exposes the
five scalar-ring operations, the three additive operations on `M`, and scalar
multiplication directly. Its body composes `chap2::is_ring`,
`is_additive_commutative_group`, and `is_module`. A nested `module.ring` or
`module.additive_group` field was rejected because it would make later vector
and normed-space access paths reflect implementation hierarchy rather than
ordinary mathematical usage.

Chapter 7's `CommutativeRing<s>` and `EuclideanDomain<s>` use the same
boundary. `CommutativeRing` exposes only the five primitive ring operations;
subtraction is the separate callable construction `gauss_sub`, not stored data.
`EuclideanDomain` exposes those five operations together with quotient,
remainder, and rank, while `is_euclidean_domain` composes
`is_commutative_ring`. The nearest rejected forms are a primitive `sub` field
constrained to equal addition with negation and a nested
`domain.ring.add/domain.ring.mul` parent path. The direct-field probe is the
Euclidean equation `domain.add(domain.mul(y,domain.quotient(x,y)),
domain.remainder(x,y)) = x`.

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
represented by a binary relation refined through the `Preorder`,
`PartialOrder`, and `LinearOrder` carrier templates rather than a
proposition-valued return type or a repeated raw relation-plus-laws signature.

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
    have fn standard_simplex_midpoint(a, b \standard_simplex<n>) fn(idx range(0, n)) R
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

`Field<K>` and `VectorSpace<K,V>` are operation-bearing flat structures.
`Field` exposes `add`, `zero`, `neg`, `mul`, `one`, and `inv`, with
`is_field` composing the Chapter 7 commutative-ring law predicate.
`VectorSpace` exposes the six scalar operations, the three vector-additive
operations, and `smul`; `is_vector_space` composes `is_field`, the Chapter 2
additive-commutative-group laws, and the scalar-action laws. The nearest
rejected forms are `field.ring.*`, `space.scalars.*`, or
`space.additive.*` parent paths. Linear maps remain candidate callable
functions satisfying `is_linear_map` between two displayed spaces; they are
not one-field records.

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

Filters and topologies are families of subsets with closure laws. `Filter`,
`Metric`, and `Topology` are refined carriers for those candidates. A
construction whose closure proof is not yet checked retains an honest raw name
such as `principal_filter_sets` or `induced_open_family`. Metric and
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

`RealNormedSpace<E>` is the checked flat ambient structure for this
source-local real differential-calculus slice. It exposes `add`, `zero`,
`neg`, `smul`, and `norm` directly, while `is_real_normed_space` composes the
additive-group, real scalar-action, and norm laws. Continuous linear maps and
Fréchet derivative relations receive source and target spaces plus candidate
functions; they do not repeat both operation bags. A
`ContinuousRealLinearEquiv` stores only its forward and inverse maps, with the
ambient spaces as parameters and the linear/bounded/inverse laws composed in
its body. The rejected forms are nested `space.vector_space.*` projections and
a proposition misleadingly called an equivalence while containing no inverse
data.

Normed-space Cauchy/completeness, continuous-linear-map, asymptotic, Fréchet,
and strict-Fréchet relationships remain implemented. The identity map has the
direct bound-one proof. Derivative selection, Rolle/MVT, finite-dimensional
completeness, operator norms, higher derivatives, and the inverse function
theorem remain in `todo.lit`.

## Measurable spaces and measure candidates

Chapter 13 keeps sigma-algebras as families of subsets closed under complement
and countable union. Countable intersection is proved by the textbook route:
complement every member, take a countable union, then complement again.

The extended nonnegative reals have not yet been constructed in Litex. Instead
of inventing a false carrier, the checked measure interface exposes the value
carrier, zero, and infinite-sum operation as parameters:

```litex
prop is_countably_additive_set_function_on(X, V set, M \MeasurableSpace<X>, zero V,
    infinite_sum fn(a fn(n N) V) V, mu fn(S power_set(X)) V)
```

`MeasurableSpace<X>` is the refined sigma-algebra carrier. The displayed
relation is a genuine generalized countable-additivity interface and supports a direct
disjoint-union theorem. It is not claimed to be Mathlib's ENNReal-valued
measure. The rejected form was a collection of trusted ENNReal, integral,
product-measure, and Jacobian selectors. ENNReal specialization, interval and
Bochner integration, dominated convergence, Fubini, convolution, and change of
variables remain in `todo.lit`.

Almost-everywhere truth is parameterized by the value carrier and its zero and
uses a measurable zero-valued exceptional set. The resulting raw family is
named `ae_large_sets`; it is not called a filter until the filter laws are
proved.

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
