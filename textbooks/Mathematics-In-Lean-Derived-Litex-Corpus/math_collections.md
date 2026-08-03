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
open-preimage property are checked for refined topology carriers; no executable
`trust`, `know`, `axiom`, or `abstract_prop` occurs in those two proof bodies.
Trust boundaries elsewhere in the corpus are explicit and indexed in the
paired workspace. Other absent source mathematics is listed in the
comment-only `todo.lit`. The project imports no Litex standard-library
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

Fermat's Last Theorem is the largest visible instance of this boundary. The
source uses an admitted proof term, but the current completion target requires
a real checked theorem. Its natural-number statement and full proof therefore
remain explicit Litex proof debt rather than an exclusion or assumption.

## Carrier-first algebra

Chapter 2 represents a generic order extensionally by a relation
`le_rel power_set(cart(A,A))`. Its associated strict comparison is the
residual relation

```litex
prop is_less_than_in_order(A set, le_rel power_set(cart(A, A)), x, y A):
    (x, y) $in le_rel
    x != y
```

The immediate source-facing use probe checks that this relation is equivalent
to non-strict comparison together with inequality. The nearest rejected form
is a new operation-bearing object or function: strict comparison is a
condition callers assert, and it introduces no selected value.

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

The same carrier-first rule applies to Chapter 2's lattice exercises.
`Lattice<s>` stores an order relation together with callable `meet` and `join`
operations. Its laws say that the relation is a partial order, `meet(x,y)` is
the greatest lower bound, and `join(x,y)` is the least upper bound:

```litex
struct Lattice<s nonempty_set>:
    le_rel power_set(cart(s, s))
    meet fn(x, y s) s
    join fn(x, y s) s
```

Distributivity is a residual property of an existing lattice:

```litex
prop is_distributive_lattice(s nonempty_set, lattice &Lattice<s>):
    forall x, y, z s:
        lattice.meet(x, lattice.join(y, z))
            = lattice.join(lattice.meet(x, y), lattice.meet(x, z))
        ...
```

The ideal semantic shape is a structure extension carrying no new operations.
The nearest rejected Litex form is a one-field `DistributiveLattice` struct
containing only the parent `Lattice`: the current struct grammar requires at
least two fields, and adding a dummy field would misrepresent the mathematics.
The property therefore records only the four distributive laws while callers
continue to use the original lattice object. Its downstream uses are the four
standard distribution projections and the equivalence of the meet-over-join
and join-over-meet formulations.

The ordered-ring examples use another residual property rather than a second
ring object:

```litex
prop is_ordered_ring(
    s nonempty_set,
    ring &Ring<s>,
    le_rel power_set(cart(s, s))
):
    ...
```

It says that `le_rel` is a partial order, addition preserves it under left
translation, and products of nonnegative elements are nonnegative. The ring
continues to supply all callable algebraic operations. The nearest rejected
form specializes the source's generic ordered-ring examples to `R`; that would
erase the source abstraction merely because real arithmetic is easier for the
verifier. Its checked consumers are the two directions of
`a <= b` iff `0 <= b-a` and monotonicity of right multiplication by a
nonnegative element.

The nearest rejected form is a collection of isolated propositions for
commutativity, associativity, and absorption. Such propositions would not give
later proofs an object whose meet, join, and order can be applied. The first
use probes are the checked commutativity, associativity, and absorption laws.

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
selection remains deferred. The componentwise product instance is now the
parameterized structure object
`product_additive_monoid_with_nsmul<A,B,left,right>`: its addition, zero, and
natural-scalar action are all explicit coordinate formulas. The tuple's
`AdditiveMonoidWithNSmul<cart(A,B)>` membership is currently one trusted law
package. A proposition-only replacement was rejected because callers need the
three structure fields. Direct field projection from the symbolic template
application currently reports that the projected function is undefined; that
caller-level verifier issue is tracked separately from the mathematical law
proof.

Chapter 8's `Module<Scalar,M>` follows the same flat-data rule. It exposes the
five scalar-ring operations, the three additive operations on `M`, and scalar
multiplication directly. Its body composes `chap2::is_ring`,
`is_additive_commutative_group`, and `is_module`. A nested `module.ring` or
`module.additive_group` field was rejected because it would make later vector
and normed-space access paths reflect implementation hierarchy rather than
ordinary mathematical usage.

The generic scalar constructions are callable templates, not propositions.
For an `AdditiveCommutativeGroup<M>`, `additive_nsmul` and `additive_zsmul`
have types `N × M -> M` and `Z × M -> M`; `integer_module` then packages the
integer ring operations, the supplied additive-group operations, and
`additive_zsmul` into `Module<Z,M>`. The nearest rejected forms are a nullary
prop saying that such an action exists and identification with builtin
multiplication on a carrier that has no multiplication. The recursive
selections and module laws remain visible trust debt.

Chapter 8's fraction quotient uses represented equivalence classes as the
carrier. `fraction_quotient_mk` maps a representative to its class,
`fraction_quotient_mul` is a selected callable satisfying the representative
equation, and `fraction_quotient_monoid` packages that operation with the class
of the original identity. This form preserves the source quotient API without
pretending that `is_fraction_class` itself is a quotient object. Projection
membership, representative independence, and the induced monoid laws remain
visible trust debt.

Chapter 9 keeps algebraic constructions callable. A normal subgroup produces
a nonempty quotient carrier together with projection, multiplication, inverse,
and a `chap2::Group` object; the projection and universal lift are functions,
not propositions. Free and presented groups likewise expose their carriers,
generator maps, and universal lifts as parameterized objects/functions, while
compatibility with relations remains a property of a candidate generator map.
The nearest rejected forms are `prop is_quotient_group(...)`,
`prop has_free_group(...)`, or `prop has_presented_group(...)` without values
that later source declarations can apply.

The quotient-group surface is now fully checked. Left-coset membership first
gives equality of cosets. Normality moves subgroup factors across
representatives, which proves representative independence for multiplication
and inverse and supports `have fn ... by exist!` selectors. Every quotient
element has a projection representative, so the source Group laws descend to
the selected operations. A homomorphism killing the normal subgroup is
constant on cosets, making the universal lift another checked unique
selection. No opaque quotient operation remains in this family.

For rings, the units of a monoid form a nonempty carrier with a callable group
object, and a ring homomorphism induces a callable map on units. An ideal
produces a quotient carrier with addition, negation, multiplication, zero and
one, packaged as a commutative-ring object; quotient projection and first-
isomorphism maps remain functions. A finite pairwise-coprime ideal family
produces a callable Chinese map and selected ring equivalence. These interfaces
depend on representative-independence and universal-property proofs.

The quotient-ring operation surface and full commutative-ring law package are
now checked. Ideal-coset membership yields equality of cosets; closure under
addition, negation, and multiplication proves representative independence and
supports three unique callable selectors. Every quotient element has a
projection representative, so the source ring laws descend through shallow
representative bridge theorems. Ideal products are checked as ordered finite
sums of pointwise products, together with their inclusions in both factors.
The kernel of a commutative-ring homomorphism is a checked ideal, and mapping a
kernel coset to the image of any representative gives a checked callable
first-isomorphism map into the range. The Chinese remainder family remains
explicit trust debt.

Polynomials are coefficient functions whose support witness is a finite subset
of `N`; allowing an arbitrary finite set with non-natural junk was rejected
because convolution must add support indices. The public surface
must include callable `polynomial_X`, constants, addition, multiplication,
power, evaluation, degree, and roots; predicates describe finite support and
being a root, but do not replace those functions. Their dependencies are the
coefficient ring, finite-support closure, finite sums, and degree/root laws.
The implemented `polynomial_X` and `polynomial_C` are uniquely selected from
their pointwise coefficient specifications with singleton natural-number
support. Addition is the checked pointwise sum, whose support lies in the union
of the two input supports. Multiplication is the checked finite Cauchy
convolution whose support is contained in the image of the Cartesian product
of the two finite natural supports under `(i,j) |-> i+j`; recursive power
iterates that multiplication. Evaluation uses the canonical nonzero
coefficient support `{n N : p(n) != zero}`, proves it finite as a subset of a
support witness, and adjoins `0`. A total selected `polynomial_eval_bound` is
characterized by membership in that nonempty finite set and domination of all
its members; these two checked projection theorems keep partial
`finite_set_max` terms out of public signatures. Existence of the characterized
maximum is one narrow `kernel_problem` trust, while selection, uniqueness,
typing, membership, dominance, finite evaluation, and the displayed root
theorem for `X + C(-r)` are checked. `polynomial_add_apply` exposes the checked
pointwise equation of the selected addition function instead of depending on
implicit unfolding; the broader function-object equality stays lexical to
that proof to keep the cross-chapter inference surface small. The
executable `polynomial_nat_degree` reuses the same finite bound. Its conditional
multiplication law remains a narrow theorem-body trust. The source's
`WithBot N` degree is not yet modeled; plain integer addition with `-1` as an
ad-hoc bottom was rejected because it gives a false zero-polynomial
multiplication law.

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

Chapter 7's permutation group uses `Equiv<s,s>` as its carrier. Because this
carrier contains the identity even when `s` is empty, `permutation_carrier<s>`
records it as a `nonempty_set`; `permutation_group<s>` is then an actual
`chap2::Group` object with reversed composition, identity, and inverse fields.
A proposition-only `is_permutation_group` wrapper was rejected because later
clients need the operations. The remaining group-record membership proof is
an extensional equality problem for composed function records.

## Source-local elementary number theory

The elementary number-theory vocabulary used across the early chapters is
defined inside this project rather than imported. Chapter 2 defines integer
divisibility by an explicit witness and defines gcd as the maximum of the
finite nonempty set of positive common divisors. Finiteness is proved in place:
the common-divisor set is bounded by a finite interval and is recovered as a
double relative complement. The gcd positivity, divisibility, greatestness,
base, and symmetry laws are ordinary checked theorems built on that definition.

Chapter 4 defines primality directly on `N+`. Chapter 5 introduces
`integer_quotient` as a callable function with `have fn ... by exist!`; the
kernel discharges only the narrow unique-existence fact for Euclidean division.
This division of responsibility is intentional: the mathematical vocabulary
and reusable proof route remain visible Litex, while arithmetic, remainder,
finite-set difference, finite extrema, and Euclidean-quotient existence are
explicit builtin boundaries. The rejected form is an empty cite package or an
imported theorem whose simple local proof is hidden from the corpus reader.

The later induction section uses native `factorial : N -> N+` and keeps
Fibonacci plus the tail-recursive Fibonacci state machine callable. The native
factorial is preferred to a chapter-local recursive duplicate because its
exact values, positivity, and successor recurrence are now kernel interfaces;
the source-facing factorial theorems remain in chapter order. Duplicate
induction syntaxes collapse to one named theorem per mathematical result. The
Fibonacci square-sum identity is a direct specialization of the checked
addition formula, while positivity of natural factors of a product equal to
one is retained as the elementary source theorem rather than as tactic-demo
residue.

## Functions, bounds, relations, and convergence

Chapters 3 and 4 distinguish functions from their graphs and properties.
Bounds and convergence are parameterized relationships; images and inverse
represented by a binary relation refined through the `Preorder`,
`PartialOrder`, and `LinearOrder` carrier templates rather than a
proposition-valued return type or a repeated raw relation-plus-laws signature.

The sequence carrier is `N`, including zero. Replacing it by `N+` was
rejected because it changes the source domain. Epsilon-N and epsilon-delta
definitions are kept even when their major analytic consequences are deferred,
because these definitions are useful downstream and have independent
mathematical content. Real sequence limits are unique: the proof chooses half
the distance between two hypothetical limits and evaluates both tail bounds at
one common natural cutoff.

Lean's truncated natural predecessor is represented by the callable function
`natural_predecessor : N -> N`, with a zero branch and the ordinary `n - 1`
branch for positive naturals. This keeps the source domain and makes the
factorial power bound well-typed at zero. The rejected form is to reuse
ordinary integer subtraction at zero, where `0 - 1` is `-1` rather than a
natural exponent. The piecewise function and the factorial power bound are
checked; no existence or well-definedness hole remains in this local
interface.

Arbitrary choice is not smuggled into an unconstrained function declaration.
Chapter 4 builds, for each target, the set of its preimages or the singleton
default when no preimage exists. Choice on this nonempty family proves
`total_inverse_exists`. The existential is then packaged as
`has_total_inverse`, and a constrained `obtain inverse` template exposes the
selected callable function:

```litex
template<S nonempty_set, T set, default S, f fn(x S) T:
    $has_total_inverse(S, T, default, f)>:
    obtain inverse from exist inverse fn(y T) S st {
        $is_total_inverse(S, T, default, f, inverse)
    }
```

The ideal interface records both branches: `inverse_spec` proves
`f(inverse(y)) = y` when a preimage exists, while
`inverse_eq_default_of_no_preimage` proves `inverse(y) = default` otherwise.
The nearest rejected form records only the first branch, since such a witness
need not agree with the source's total choice-with-default definition outside
the range. The checked downstream probes are the source equivalences between
injectivity and the selected inverse being a left inverse, and between
surjectivity and it being a right inverse.

Chapter 4 also exposes the source-ordered `sb_aux`, `sb_set`, and `sb_fun`
constructions. The right-inverse lemma, closure of `sb_set` under `g o f`, and
the injective and surjective branches of `sb_fun` lead to the final explicit
Schröder–Bernstein bijection witness. The exact zero, successor, and two
piecewise computation equations currently form a visible four-trust
`kernel_problem` boundary because template computation facts are not exported
to later verification. Thus the source family is fully translated and
executable, but it is not checkable until those four equations are discharged.

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

Chapter 5's prime-factor multiplicity is a callable arithmetic function:

```litex
trust have prime_factor_exponent fn(n, p N) N
```

Its intended value is the exponent of `p` in `n`, with the source convention
at zero.  Later statements apply this function in the multiplication, power,
prime-self, parity, and power-equation laws.  A proposition such as
`has_prime_factor_exponent(n,p,k)` is not a replacement because downstream
mathematics needs the selected exponent.  Until decreasing division or an
equivalent finite-maximum construction is available, the function's existence
and the exact source laws remain explicit proof debt.

The source's `MyNat` is likewise kept as a genuinely independent nonempty
carrier, not aliased to builtin `N`.  Its zero and successor are named objects,
its induction rule is an ordinary universal fact, and addition and
multiplication are callable binary functions with the source recursion
equations.  The nearest rejected form is a `prop` describing Peano arithmetic:
callers must be able to construct successors and evaluate arithmetic.  The
carrier, constructors, recursive selections, and their computation equations
remain trusted until Litex supports user-defined inductive carriers and their
recursors; the algebraic laws are stated separately in source order.

Chapter 6 applies the same boundary to `BinTree` and `PropForm`. Each is an
independent nonempty carrier with named constructors and a structural
induction interface. Tree size, depth, and flip, and formula evaluation,
variable support, and substitution are callable functions. Representative
signatures are:

```litex
trust have binary_tree_size fn(tree BinaryTree) N
trust have formula_eval fn(formula PropForm, valuation fn(idx N) {0, 1}) {0, 1}
trust have formula_subst fn(formula PropForm, idx N, replacement PropForm) PropForm
```

The nearest rejected form is a collection of predicates that only says a
candidate value is a size, evaluation, or substitution result. Source
theorems evaluate and compose these functions, so the functions themselves
must remain visible. Their constructors, recursors, computation equations,
and structural-induction theorems currently form explicit proof debt.

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
2. define the quotient carrier and its canonical source-to-class projection;
3. prove representative independence for proposed quotient operations;
4. only then expose those operations and universal lifts.

The current chapters implement several relations, cosets, and quotient
carriers. Chapter 10 also exposes the canonical callable projection
`quotient_projection(U,v) = v + U`, proves its codomain membership and the
quotient carrier's nonemptiness, and proves that every quotient element is in
its image. This projection needs no quotient operation: it only packages the
representative already present in the carrier definition. The chapters do not
postulate steps 3 and 4. The rejected form is an opaque selected
multiplication or lift whose well-definedness is hidden. Normality, ideal
membership, or kernel containment must be visible in any future
implementation. Quotient monoids, quotient groups/rings/spaces, first
isomorphism theorems, and CRT therefore remain explicit todo families.

## Gaussian integers and polynomial carriers

Gaussian integers are coordinate pairs with direct addition, multiplication,
conjugation, norm, and rank functions. Projection, norm-zero, positivity,
multiplicativity, conjugation, and the checked rank inequality form a usable
core. The source-facing `gaussian_integer_commutative_ring` now packages the
five callable coordinate operations as a `CommutativeRing<GaussInt>` object.
Its single `is_commutative_ring` law package remains explicit trust until the
coordinatewise additive, multiplicative, distributive, identity, inverse, and
commutativity proofs are supplied. A proposition-only assertion was rejected
because later mathematics needs the operations through a real structure
value. The Euclidean-domain construction still depends on centered division
and a strict remainder-norm proof, so it remains deferred.

Polynomials are coefficient functions with a support witness that is both
finite and contained in `N`. This is the right carrier because coefficient
lookup is direct and later arithmetic can add support indices through finite
sums. The nearest rejected forms are an arbitrary finite support containing
non-natural junk, or opaque multiplication/evaluation functions with no
finite-sum construction. X and constants use singleton supports, addition uses
their union, multiplication uses the finite image of the support product, and
power recursively uses multiplication. Evaluation is an ordered finite fold
over a canonical support bound, not an opaque operation. Composition, roots
beyond the defining predicate, and source-faithful degree theory remain
downstream.

## Linear algebra

Chapter 10 builds from fields, vector spaces, and linear maps to binary product
and coproduct maps, subspaces, span, kernels, ranges, quotient carriers,
eigen-data, concrete matrices, and basis relationships. Pointwise addition and
scalar multiplication preserve linearity, fixed-scalar endomorphisms are
linear, linear maps preserve zero, and their images and preimages of subspaces
are subspaces. The bottom and top carriers are checked subspaces, as are the
intersection of two subspaces and the kernel and range of every linear map.
The image/preimage constructors satisfy the checked map/comap subset
adjunction. The span contains its generators, is itself a subspace, and
satisfies the full checked subset adjunction against every subspace.
Linear maps preserve additive inverses; injectivity is equivalent to having
bottom kernel, and surjectivity is equivalent to having top range. Linear-map
composition follows its short natural proof and now concludes directly about
the canonical `linear_map_compose_raw` function. Consequently
`endomorphism_comp` is a typed callable operation on `endomorphism_space`, not
an arbitrary function-valued alias. The quotient carrier is nonempty, and its
typed canonical projection is callable and surjective. A quotient vector-space
structure and the projection's linear-map laws remain downstream of
representative-independent addition and scalar multiplication. The raw
pointwise sub-scalar map `v |-> phi(v) - a v` is proved equal to the sum of
`phi` and `-1` times the scalar endomorphism. The checked addition and scalar
closure laws therefore make `endomorphism_sub_scalar` a typed callable
endomorphism, and the canonical eigenspace theorem identifies the eigenspace
with its zero kernel.

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

Because this corpus stores the six scalar-field operations directly in every
`VectorSpace<K,V>`, a product-space constructor must require the left and
right spaces to agree on those operations; sharing only the carrier name `K`
is insufficient in the flat model. Under those compatibility equations the
product uses coordinatewise vector addition, zero, negation, and scalar
multiplication, while retaining the common left-hand scalar operation package.
The nearest rejected form is an unconditional product selector, which would
silently combine potentially different field structures on the same carrier.
The coordinate laws and both universal maps are checked: pairing two linear
maps into the product is linear, and copairing two linear maps out of the
factors is linear. Small named coordinate-law theorems keep verifier search
bounded and expose reusable facts.

Dependent direct sums, quotient operations, endomorphism polynomials, basis
coordinates, finite indexed matrix sums, and dimensions require additional
objects. Their ideal forms are callable functions or selected values justified
by existence and uniqueness; turning them into propositions was rejected. The
finite-dimensional interface remains an existence relationship for a finite
basis, which supports later hypotheses without claiming a selected dimension.
The homogeneous direct-sum inclusion is selected by its pointwise
characteristic relation: it has the supplied value at the chosen coordinate
and zero elsewhere. Its singleton support supplies existence, while function
extensionality supplies uniqueness. This keeps `direct_sum_single(idx, v)`
callable and exposes the two coordinate equations used by later universal
properties. This selection and its support proof are checked; the finite-sum
universal lift remains proof debt. Its ideal interface must include both the
source zero used to define finite support and a target commutative additive
monoid:

```litex
template<
    I set,
    V, W nonempty_set,
    zeroV V,
    addW fn(x, y W) W,
    zeroW W:
    $chap9::is_additive_commutative_monoid(W, addW, zeroW)
>:
    have fn direct_sum_lift(
        phi fn(idx I) fn(v V) W,
        value \indexed_direct_sum<I, V, zeroV>
    ) W
```

Mathematically this is the finite sum of `phi(idx)(value(idx))` over any
finite support. The target zero is required for the empty support and for
ignoring extra zero coordinates; associativity and commutativity make the
value independent of enumeration. The former signature with only `addW`
cannot define the empty sum or justify that different support witnesses and
orders give the same result. The required upstream node is therefore a
generic finite commutative-monoid fold with insertion, zero-summand, and
reindexing laws; the numeric-only `finite_set_sum` surface is not an adequate
substitute.

Polynomial endomorphism evaluation now has a correctly typed callable surface:
`endomorphism_pow` stays in the checked endomorphism carrier, and
`endomorphism_finite_sum` folds endomorphisms using checked pointwise addition.
Their callable declarations are checked recursive definitions, and their exact
zero/successor equations are checked named theorems. The shared solution is
branch-aware predecessor carrier and decrease checking, not a special
polynomial-endomorphism rule. Downstream term and evaluation functions are
typechecked against those interfaces.

The resumed Chapter 10 slice exposes those missing constructions at their
usable semantic level. A linear equivalence is a forward linear map together
with a callable inverse and two inverse laws; composition and inversion should
therefore return functions, not merely assert equivalence propositions.
Binary and dependent products use function or Cartesian-product carriers with
callable projections and inclusions. A finite-support direct sum is a refined
dependent-function carrier, and its inclusion and universal lift are callable
maps. Proofs that these operations are linear may remain narrow trust debt, but
the objects themselves must remain available to downstream statements.

Subspace inheritance, internal direct sums, and quotient spaces similarly need
operation-bearing selected structures. The real axis is a concrete subspace
candidate; an inherited subspace space reuses ambient operations on a refined
carrier. Because Litex represents a subspace here as a `power_set(V)` rather
than a structure-valued `Submodule`, `is_complementary_subspaces` includes the
two subspace laws and the decomposition-existence interface explicitly in
addition to top join and bottom intersection. Uniqueness remains a checked
consequence of the bottom intersection. This makes the selected decomposition
depend on the same mathematical data that Lean's submodule types and complement
theorems provide together. The nearest rejected form is a complement predicate
over two arbitrary subsets, from which closure and decomposition cannot be
used. Quotient addition, negation,
scalar multiplication, and projection form a selected `VectorSpace`, while
compatible maps receive callable quotient lifts. The nearest rejected quotient
form is a predicate named “quotient space” with no operations or projection.
First-isomorphism and correspondence interfaces are maps between the displayed
quotient, range, and subspace carriers.

Polynomial evaluation at an endomorphism consumes the Chapter 9 finite-support
polynomial carrier and returns an endomorphism. This interface is now checked:
the constant-zero function, pointwise addition and scalar multiplication, and
scalar maps are first exposed as typed endomorphisms; natural powers iterate
typed composition from the scalar identity; a specialized ordered recursive
sum stays in the endomorphism carrier; and evaluation sums coefficient-scaled
powers through Chapter 9's canonical polynomial support bound. The rejected
form is an opaque function-valued selection with no closure proof. The
following coprime-kernel theorem still needs the evaluation homomorphism laws
for polynomial addition, multiplication, and constants.

Minimal and characteristic polynomials are selected polynomial objects only
under the finite-dimensional hypotheses that justify them; Cayley–Hamilton is
their evaluation law. Matrices are indexed functions, bases have callable
coordinate maps, and change of basis is a callable matrix transformation.
General matrix multiplication is implemented by the checked ordered
finite-range sum, and the identity matrix is a checked piecewise indexed
function. Determinant, inverse, basis-coordinate selection, reconstruction,
and dimension/cardinality proofs remain the explicit trust boundary. The
rejected forms are opaque theorem predicates standing in for coordinates,
matrices, or polynomial evaluation.

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

The foundational candidate-distance predicates `metric_separates_points` and
`is_metric_space` occur first in Chapter 2, where the source introduces the
metric laws and proves distance nonnegativity. Chapter 11 reuses those
predicates and introduces the refined `Metric` carrier plus balls, convergence,
compactness, and completeness. The rejected form is a second Chapter 11 copy
of the same metric laws, because duplicate predicates would make later metric
objects depend on a different interface from the source's first example.

The checked `topologically_continuous_composition` theorem is ordinary
composition between three fixed topologies. The retained source item instead
asks for an iff after replacing the middle topology by the topology coinduced
along the first map. That topology-changing composition equivalence remains
explicit source debt in `todo.lit`; ordinary composition does not discharge
it.

The next general-topology slice keeps `coinduced_open_family` and
`induced_open_family` as callable open-set families and promotes each by a
separate theorem showing membership in `Topology`. Comparisons, changed-
topology continuity, neighborhood bases, dense extension, sequential closure,
cluster points, and compactness are theorem relationships over explicit
topology and filter carriers. The nearest rejected form is a proposition named
“induced topology” or “compact object” that exposes neither the open sets nor
the filters used downstream. Chapter 11's former five executable
`kernel_problem` boundaries now check: the two exact
`tends_to_by_preimage` packages use the bounded definition-folding fallback,
and the serial relation, path step, and first-countable compact-subsequence
proofs use their explicit proof bodies. The still-unproved dense-extension
claim remains an explicitly named non-executable goal proposition.

This definition-first layer is retained because it gives later theorems the
right hypotheses. The rejected form is to add a large collection of theorem-
shaped propositions at the top of the chapter. Actual proof spines now check
for the filter algebra used here, closure characterization, the reverse Cauchy
bridge, compact-set closedness, Baire, compact subsequences, and finite
subcovers. Real interval compactness, compact extrema, and dense extension
remain visible in `todo.lit` as proof goals rather than executable facts.

For the resumed filter and metric slices, the raw principal, map, comap, and
at-top families are promoted by explicit filter-law theorems; this preserves
their set-family definitions while making their refined-filter status usable.
Real limit algebra remains stated on the chapter's epsilon formulation.
Metric compactness, uniform continuity, the reverse Cauchy bridge, geometric
step convergence, and Baire are theorem relationships over the existing
metric objects. The Baire conclusion is density of the callable countable
intersection, not a proposition-shaped replacement for that set. These
supporting proofs, including the nested-ball construction and closed-cover
consequence, are checked.

The remaining elementary metric examples use the same layer: distance of two
continuous maps is a real-valued continuous map; limits of sequences in a
closed set stay in the set and hence lie in its closure; and compact metric
subsets are closed. Real closed-unit-interval compactness remains an explicit
goal pending a checked real-completeness or Bolzano–Weierstrass interface. The
compact-space universe theorem unfolds directly from
`is_compact_metric_space`. Repeated Lean proof variants and
neighborhood-basis displays collapse to the callable ball, closed-ball,
closure, and continuity definitions already present.

Compactness keeps the source's filter characterization as its core
topological relation. The first-countable subsequence theorem adds a witness
point in the compact set and a strictly increasing natural reindexing.
Continuous images and cluster-point mapping are theorem relationships over
the existing image, continuity, convergence, and compactness interfaces. A
finite indexed subcover is represented by a natural length and a choice
function whose first `n` values are indices; this preserves the mathematical
finite-subfamily witness without requiring a separate `Finset` construction.
The rejected form is a proposition called “subsequence” or “finite subcover”
that contains no callable reindexing or selected indices. The mapped-cluster
and finite-subcover theorems have checked proof bodies. The compact-image proof
folds its exact preimage-convergence definition after the universal membership
construction. The compact-subsequence wrapper, seriality proof, path-step
elimination, and complete witness construction are all checked. The
finite-subcover index
carrier is explicitly nonempty because its witness representation contains a
total natural-number choice function.

The C11 pressure test exposed a kernel bug in which automatic universal-fact
matching replaced a non-quantified free set parameter. The matcher now treats
only the fact's own quantified header as instantiable and keeps captured outer
parameters rigid. Eventuality and limit proofs still call small projection
theorems with every set and filter argument explicit because that interface is
mathematically clear; the former counterexample is retained as a rejecting
kernel regression rather than live proof debt.

## Images, preimages, and indexed set operations

Restricted image and preimage are callable set constructions, not predicates:

```litex
template<S, T set, f fn(x S) T, A power_set(S)>:
    have set_image power_set(T)
template<S, T set, f fn(x S) T>:
    have fn set_preimage(B power_set(T)) power_set(S)
```

Binary intersection, union, and difference also have source-local callable
forms whose return type is explicitly `power_set(X)`. This matters when the
result is passed directly to another typed construction: the raw builtin set
operation currently does not always retain the refined carrier in that
position. Indexed images are likewise represented by a named function family
instead of repeating an anonymous function inside theorem conclusions. The
nearest rejected forms are proposition-shaped “image” objects and theorem
statements padded with separate membership facts solely to repair expression
typing. The elementary image/preimage laws remain narrow trust debt while the
objects and theorem interfaces themselves are executable.

## Differential calculus

A derivative is first a relationship between a function, a point, and a
candidate linear value or map:

```litex
prop has_derivative_at(f fn(x R) R, x0, L R)
prop has_frechet_derivative_at(E, F set, ..., f fn(x E) F,
    fprime fn(x E) F, x0 E)
```

This representation supports honest hypotheses without selecting a derivative.
A total `deriv`, `fderiv`, or local inverse should be exposed only with the
needed uniqueness or existence boundary visible. For the resumed elementary
slice, `real_deriv` is a callable selected value and its differentiable and
nondifferentiable laws are explicit trusted library debt. Sine and pi are
similarly visible background objects with only the laws used by the source
examples. The rejected form is a predicate named `deriv` or a numeric
stand-in that cannot be called by Rolle, mean-value, and evaluation theorems.

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
direct bound-one proof. The operator norm and pointwise Fréchet derivative are
callable selected objects, and their characteristic upper-bound, least-bound,
and derivative-identification laws are explicit localized trust boundaries.
Positive nested law packages now project recursively, so norm nonnegativity,
the norm triangle inequality, and continuous-linear-map additivity and scalar
compatibility are checked directly. Grouped universal conclusions also project
over their used nonempty parameters, so scalar norm compatibility is checked
despite sharing a binder with the other scalar laws. Classical implication
packaging also checks the zero-norm iff wrapper from the two directional laws.
This is preferable to predicates named `operator_norm` or `fderiv`, since
source expressions apply and compare the selected objects. Their actual
supremum/uniqueness constructions, finite-dimensional completeness, higher
derivatives, and the inverse function theorem remain in `todo.lit`.

Banach–Steinhaus is implemented as a real-scalar specialization because
`RealNormedSpace` is the chapter's established ambient interface. Continuity
of every indexed map and pointwise boundedness are deliberately separate
properties:

```litex
prop is_continuous_real_linear_map_family(Index, E, F, source, target, g)
prop is_pointwise_bounded_map_family(Index, E, F, target, g)
prop is_uniformly_bounded_continuous_linear_map_family(
    Index, E, F, source, target, g)
```

The nearest rejected form bundles continuity into pointwise boundedness. Those
are independent hypotheses mathematically, and the proof needs to project
each one separately. The natural-number level sets are a callable template,
not a proposition standing in for a set:

```litex
pointwise_bound_level_set(n)
    = {x : E | forall j, norm(g(j)(x)) <= n}.
```

The dependency path is pointwise bounds --definition--> level sets
--proof--> closed cover --checked Chapter 11 closed-cover Baire--> a level set
containing a ball --proof--> a common annular
bound --proof/trust--> an operator-norm bound. The annular rescaling arithmetic
and final family aggregation are checked. Visible trust edges remain at
closedness of the indexed level sets, the Archimedean natural bound, transport
between the two completeness formulations, the additive recentering estimate,
and the general shell-to-operator-norm lemma. Thus the source theorem and its
proof spine are executable, but the Chapter 12 declaration is translated
rather than trust-free checkable.

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

Elementary integration now starts with callable oriented-interval and
whole-real-line integral operators. Their construction is an explicit trusted
analysis-library boundary; source theorems consume those same operators, and
real convolution is a callable function defined by the whole-line integral.
The nearest rejected form is five independent propositions which happen to
mention integral formulas but provide no integral or convolution object for
later chapters.

Almost-everywhere truth is parameterized by the value carrier and its zero and
uses a measurable zero-valued exceptional set. The resulting raw family is
named `ae_large_sets`; membership in that family is connected to
`holds_almost_everywhere` by an explicit checked source-facing equivalence.
It is not called a filter until the filter laws are proved.

## Checked/deferred ownership

Executable chapter files contain definitions, constructions, and facts
accepted by the ordered project runner. Chapter 7 currently has one explicit
trusted Gaussian commutative-ring law package; `todo.lit` records that proof
debt and all other known unimplemented source mathematics. The ledger is
comment-only and absent from `litex.config` exports.

When a todo family is resumed, first reconstruct its natural-language proof or
construction, then restore the smallest source-facing declaration in source
order and run a representative use probe. Only after the implementation passes
should the matching todo paragraph be removed and its JSONL record changed
from `blocked` to `verified`.
