# Mathematics in Lean C01-C13 mathematical collections

This manual records the mathematical shapes that organize all thirteen
chapters. It is deliberately smaller than the item-by-item source manifest:
only concepts that determine later declarations or proof architecture belong
here.

Source snapshot: *Mathematics in Lean* at
`6dfa2c166a410d2f0f278d327ea81ae0fa6d3c32`.

## Closed facts and reusable properties

Fermat's Last Theorem is a closed universal mathematical assertion. The Lean
source first names a proposition-valued term `FermatLastTheorem`, then the
theorem `hard` supplies a term of that proposition using `sorry`. In this
Litex textbook those two source steps become one direct fact:

~~~litex
trust:
    forall x, y, z, n N:
        n > 2
        x * y * z != 0
        =>:
            x^n + y^n != z^n
~~~

The rejected form was `prop fermat_last_theorem()` followed by
`trust $fermat_last_theorem()`. A `prop` is appropriate when later mathematics
tests a candidate against a reusable property or relation, as in `even(n)`;
it is not an extra box around a closed assertion. The Fermat fact depends only
on natural-number arithmetic, can be specialized directly at any exponent
greater than two, and retains exactly one proof hole: the source's `sorry`.

## Carrier-first algebra

The source's rings and groups are generic structures, not facts specifically
about real numbers. Their Litex form therefore starts with a carrier and makes
each operation explicit:

~~~litex
prop is_ring(A set, add fn(x, y A) A, zero A, neg fn(x A) A,
    mul fn(x, y A) A, one A)
~~~

This matters because the cancellation, zero-product, identity, and inverse
theorems should remain reusable for any carrier satisfying the displayed laws.
The nearest rejected form was to specialize every theorem to `R`, which would
change the source mathematics while making the proofs easier. These interfaces
depend only on ordinary equality and explicit operations. Direct elementary
consequences are checked where possible; later quotient, selected-carrier, and
finite-sum constructions retain their own visible debt.

## Function bounds, symmetry, and convergence

Chapter 3 packages recurring analytic hypotheses as properties:

~~~litex
prop is_upper_bound_of_fn(f fn(x R) R, a R)
prop is_even_fn(f fn(x R) R)
prop converges_to(s fn(n N) R, a R)
~~~

Bounds support witness-based closure results, even and odd functions support
the symmetry examples, and convergence supplies the chapter's epsilon-N
theorem chain. The index carrier of a sequence is `N`, including zero; using a
positive-only sequence alias was rejected because it would alter the source
domain. Generic Lean variants over an arbitrary ordered carrier are not
specialized silently. A binary order is represented extensionally by
`le_rel power_set(cart(A,A))`, with `(x,y) $in le_rel` as relation application.
This carrier-first representation supports explicit preorder, partial-order,
and linear-order laws, generic function/set bounds, and generic indexed
convergence without requiring a function whose return type is `prop`.

## Total inverse and Schroeder-Bernstein

The source inverse is a total choice function. Given a preimage it selects one;
otherwise it returns a supplied default. Its ideal Litex form is callable and
carrier-dependent:

~~~litex
template<S, T set, default S>:
    have inverse fn(f fn(x S) T, y T) S
~~~

Replacing this object by a proposition, or restricting it to bijections, was
rejected because either choice loses the source construction. The inverse
feeds `sb_aux`, `sb_set`, and the piecewise `sb_fn`, which in turn supplies the
final Schroeder-Bernstein witness. Arbitrary choice, recursive functions inside
carrier templates, and the stage-membership transport proofs remain visible
trusted boundaries. The final assembly from injectivity and surjectivity to a
bijection is checked.

## Prime-factor exponent and recursive arithmetic

Prime multiplicity is a function, not merely a predicate:

~~~litex
have prime_factor_exponent fn(n, p N) N
~~~

It connects irrational-root arguments to factorization product and power laws.
The nearest rejected model was a proposition that only asserted the existence
of an exponent, because downstream formulas must call the exponent. It depends
on primality, divisibility, and gcd from `std/basics`. The construction and its
substantial factorization theorems remain proof debt in this first edition.

Factorial, finite sums, and Fibonacci numbers are ordinary recursive callable
objects. Their definitions are checked with `have fn ... by induc`; longer
induction theorems may retain theorem-local trust without changing the
functions' public types.

## The source MyNat carrier

`MyNat` is the book's separate Peano construction, not a new spelling of
Litex's builtin `N`. The closest faithful current form keeps an opaque carrier,
zero, successor, addition, multiplication, and their equations as explicit
trusted objects. Identifying the carrier with `N` was rejected because it would
erase the construction being taught. Checked user-defined inductive carriers,
constructor principles, and induction over them are the remaining language
hole; the downstream algebraic theorem statements stay source-faithful and
visible.

## Discrete inductive interfaces

Chapter 6 keeps the source's list, tree, and propositional-formula vocabulary
separate from builtin finite-set arithmetic. `ListCore` records a carrier plus
callable `nil` and `cons`; append and map remain callable selected functions,
not existential properties. Binary trees and formulas likewise retain opaque
carriers and typed constructors where user-defined inductive types or generic
structural recursion are unavailable. Their induction conclusions are named
theorems with local trust, while finite-set/cardinality identities stay direct
when the existing finite-set surface suffices.

## Structures, quotients, and algebraic hierarchy

Chapters 7–9 use `struct` for records that actually store operations and laws,
and `prop` only for relations on supplied candidates: for example, a subgroup,
normal subgroup, homomorphism, or ideal. Gaussian integers, scalar actions,
maps, cosets, quotient carriers, and polynomial evaluation are functions or
objects whenever later declarations call them.

Quotient operations require their mathematical guards to remain explicit:
commutativity or normality for representative operations, and compatibility or
kernel containment for a lift. A selected quotient projection, multiplication,
inverse, or lift may be trusted, but its type and exact compatibility premise
remain visible; no quotient well-definedness is replaced by a bare property.

## Linear algebra and dependent families

Chapter 10 keeps a vector space on explicit scalar and vector carriers.
`is_linear_map`, `is_subspace`, eigenvalue conditions, basis conditions, and
finite-dimensionality are reusable relations. Direct products/sums carry their
explicit family parameter; quotient lifts display both their subspace and
kernel-containment compatibility premises. Kernel/range and eigenvalue
equivalences are recorded as directional theorem facts. `Basis_mk` consumes an
`is_basis` witness and returns its `basis_space`, while coordinate/matrix
interfaces retain their finite-support and index guards. These constructions,
matrices, and dimensions are objects or callable functions because downstream
statements apply them. Missing dependent-family, finite-support, quotient,
basis-selection, or dimension constructions therefore own typed object trust;
theorems such as Cayley-Hamilton retain theorem-local trust rather than becoming
proposition wrappers.

## Topology, calculus, and integration

Chapter 11 represents filters as families of large sets, metric/topological
structures as properties of explicit data, and balls, closures, induced
topologies, and filters as sets or functions. A source equivalence becomes the
two source-faithful facts `..._forward` and `..._reverse` when Litex cannot
state that equivalence as one top-level theorem conclusion.

Chapters 12–13 preserve the same distinction across analysis: differentiability,
continuity, asymptotic, measurability, and integrability conditions are
relations; derivatives, norms, operator norms, local inverses, measures,
integrals, product measures, and convolution are callable objects. The
analytic headline results remain theorem facts with local proof debt, rather
than being recast as `prop` declarations.

## Trust ownership

Trust stays at the smallest declaration or fact that owns the missing
construction or proof. A `trust` body must be a literal typed declaration or
the exact fact being deferred; prose after `trust:` is not an executable proof
boundary. Shared assumptions would belong in `citation.lit`; chapter-local
debt remains at its source-facing declaration. Repeated tactic scripts are
collapsed, and a trusted item is never described as a checked proof.
