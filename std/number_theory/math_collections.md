# Divisibility and congruence

An integer multiple witness is the starting point: d divides a when a=k*d for some integer k. The native predicate `$dvd(a,d)` already represents this relation with dividend first and d in Z*. It is reused directly; in particular this package does not extend divisibility to a zero divisor or introduce a second argument convention. Integer multiplication of witnesses proves transitivity; distributing two multiples proves closure under integer linear combinations.

Congruence is a relation between supplied integers, not a selected residue value:

```litex
prop is_congruent_mod(a, b Z, modulus N+):
    $dvd(a - b, modulus)
```

The positive integer modulus belongs to the relation's own signature. Modulus 1 and zero or negative operands are legitimate. `%` and `quot` remain the native constructions for Euclidean remainder and quotient. No residue class set or quotient ring is selected by this predicate.

The dependency direction is integer multiple witnesses -> divisibility transitivity and linear combinations -> congruence equivalence and compatibility with addition, subtraction and multiplication. Scaling and negation follow from multiplication. Native Euclidean decomposition supplies congruence with the remainder. Divisibility transitivity weakens a congruence from n to a positive divisor m of n.

Multiplication compatibility does not permit unconditional cancellation: 2*1 and 2*4 are congruent modulo 6, while 1 and 4 are not. The extension below supplies inverse relations and cancellation given an inverse. General Bezout or inverse existence, CRT and primality development require further mathematics, rather than extra clauses in congruence.

## Euclidean transformations and supplied inverse relations

Native positive gcd on integer pairs not both zero remains the only gcd value.
For b nonzero, linear-combination divisibility and the native common-divisor
bound prove gcd(a+k*b,b)=gcd(a,b). Integer-multiple witnesses then transport
gcd along congruence; positive-divisor Euclidean decomposition gives the
remainder step. A solution of a*x+b*y=c forces gcd(a,b) to divide c. A supplied
Bezout identity a*u+b*v=d and d dividing c gives a solution by scaling; this
does not assert universal Bezout existence.

is_modular_inverse(a,u,m) is a relation about a supplied integer u, defined by
is_congruent_mod(a*u,1,m), m positive. It is not a selected inverse value. A
supplied Bezout identity with right side1 proves that relation. It then permits
cancellation, gives a solution u*b to a*x congruent b, and proves uniqueness
modulo m, including uniqueness of the supplied inverse itself. No unnecessary
coprime hypothesis is added, and no existence theorem is inferred from the
relation. Modulus1 remains legitimate. All-zero gcd, zero/negative modulus and
missing inverse/Bezout premises retain their actual boundaries. The source proofs and full-domain imported calls verify without user trust or
axioms. Exact native domains remain visible; no new native rule is needed.


## Natural powers and congruence

Congruence is reflexive at exponent zero and respects multiplication, so
induction gives congruence of equal natural powers for arbitrary integer bases.
A supplied modular inverse yields `(a*u)^n ≡ 1`; natural-power distribution
then gives `a^n*u^n ≡ 1`. The remainder result applies the power theorem to
the existing `a ≡ a%m` law. Positive moduli, including 1, and zero exponent
are preserved; `0^0=1` is the existing Litex convention. No inverse existence,
negative exponent, selector, axiom or native rule is introduced. All 19 focused
checks pass, including 11 final-only refusals and both installed layouts.
