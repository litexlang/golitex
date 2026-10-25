# Abstract Algebra in Litex

These lecture notes develop the group part of abstract algebra, with integer
addition as a running example. Familiar calculations lead to group laws;
those laws lead to cancellation and subgroups; structure-preserving maps then
lead to kernels and a criterion for injectivity.

Read [abstract_algebra.lit](abstract_algebra.lit) from beginning to end.
The central Litex idea is that a structure packages operations and laws,
while later proofs use those laws to establish new facts. The same interface
supports both abstract arguments and concrete integer examples.

The group structure, subgroup and homomorphism predicates, kernel construction
and twelve general theorems come from [std/algebra](../../std/algebra/README.md).
The lecture imports that package as `Algebra` and retains the integer examples
and the theorem about multiples. Read the library's
[group.lit](../../std/algebra/group.lit) for the shared proofs.

## From addition to group laws

The notes begin with two operations and a calculation:

```litex
have fn integer_add(x, y Z) Z = x + y
have fn integer_neg(x Z) Z = -x

integer_add(3, -3) = 0
```

These operations, together with zero, form the integer additive group.
The general `Group<A>` interface uses multiplicative names: in this example,
`integers.mul` is addition, `integers.one` is zero and `integers.inv` is
negation. Commutativity is a separate property, so the general group theorems
also apply to noncommutative groups.

Associativity and inverses give cancellation. Cancellation then proves
uniqueness of the solution to `G.mul(a, x) = b`. Subgroups keep the ambient
operations: integer multiples form subgroups, whereas nonnegative integers
fail because the inverse of `1` is missing.

## From homomorphisms to kernels

A homomorphism is required to preserve only the group operation. The
following is the definition in the library's own `group` export:

<!-- litex:skip-test -->
```litex
prop is_homomorphism(A nonempty_set, G &Group<A>, B nonempty_set, H &Group<B>, f fn(x A) B):
    forall x, y A:
        f(G.mul(x, y)) = H.mul(f(x), f(y))
```

Preservation of the identity and inverses are proved consequences.
For the identity, `f(G.one)` is equal to its own square; cancellation forces
it to be `H.one`. For inverses, preservation of multiplication produces an
inverse pair, and uniqueness identifies the image of the inverse.

The kernel is the subset of elements sent to `H.one`. It is a normal
subgroup even when the domain is not abelian. The final theorem pair proves
that a homomorphism is injective exactly when only the identity maps to the
identity. This gives two contrasting concrete outcomes, shown here as an
excerpt using the notes' earlier declarations:

<!-- litex:skip-test -->
```litex
\Algebra::group::kernel<Z, Z, integers, double> = {0}
\Algebra::group::kernel<Z, Z, integers, zero_map> = Z
```

Doubling preserves addition and loses no information. The zero map also
preserves addition, but sends every integer to zero. Translation by one
provides a different counterexample: it fails to be a group homomorphism
because it does not preserve the identity.

## Reading guide

| Sections | Mathematical progression |
|---|---|
| 1.1 | Integer operations; groups; an abelian concrete instance |
| Shared library | Identity and inverse uniqueness; left and right cancellation; unique equation solutions |
| 1.3 | Subgroups; integer multiples; a nonnegative-integer counterexample; intersections |
| 2.1 | Homomorphisms; preservation of identity and inverse; doubling and translation |
| 2.2 and shared library | Kernel subsets; normal subgroups; normality in abelian groups; general kernel normality |
| 2.3 | Trivial kernels and injectivity in both directions; doubling and zero-map kernels |

These are original, selected lectures, not a textbook translation or a
complete abstract algebra course. Quotient-group construction, Lagrange's
theorem, rings, modules and Galois theory are outside this slice. The existing
[abstract algebra concepts showcase](../math_concepts_in_litex/6_abstract_algebra/README.md)
contains a separate development of commutative rings and quotient presentations.

The complete lecture passes strict Litex verification and contains no user
`trust`, `axiom` or `abstract_prop`. Verification uses Litex's own verifier
and builtin mathematical rules; no Lean certification is claimed.

[math_collections.md](math_collections.md) explains the mathematical organization
and interfaces. [litex.config](litex.config) exports the lecture as
`abstract_algebra`. For command-line usage, see the [CLI documentation](../../docs/cli.md).
