# Conjugation in a group

For an arbitrary Group, conjugation by `a` maps `x` to `(a*x)*a^{-1}`.
The existing Group operations yield identity, product and inverse preservation,
two inverse-action identities, and a bijective homomorphism. Multiplication need
not commute. Two elements commute exactly when conjugating one by the other
fixes it; a group is abelian exactly when all conjugations fix all elements.
The following isolated consumer calls the homomorphism theorem:

```litex
thm consume_conjugation_is_homomorphism:
    ? forall A nonempty_set,G &Algebra::group::Group<A>,a A:
        $Algebra::group::is_homomorphism(A,G,A,G,fn(x A) A {G.mul(G.mul(a,x),G.inv(a))})
    release thm Algebra::group::conjugation_is_homomorphism(A,G,a)
```

The [generic contracts](contracts/main.lit) exercise all twelve theorem
interfaces. The [one-element group](trivial/main.lit) checks the degenerate
case, and the [integer additive group](integers/main.lit) checks both directions
of the abelian characterization. The [Heisenberg example](noncommutative/main.lit) obtains
`(1,0,0)*(0,1,0)*(1,0,0)^(-1) = (0,1,1)`, proves this is not `(0,1,0)`,
and checks the bijection, homomorphism and product law. The example reuses
the checked noncommutative model from [groups](../groups/noncommutative/main.lit).

The [negative controls](negative/expected.json) reject unconditional claims
that conjugation fixes every element, reverses products, or agrees with the
inverse conjugation, as well as a constant bijection and an invalid carrier.
A refusal is a failure to verify, not by itself a proof of negation; the
Heisenberg result supplies a concrete nonidentity witness.

Run `python3 examples/algebra/conjugation_laws/check.py --binary /path/to/litex
--output-dir /path/to/results` for strict source, consumer, boundary and
installed-layout checks. No quotient, new conjugation selector, native rule or
additional axiom is introduced.
