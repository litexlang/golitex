# Mathematical collections and interfaces

The book develops elementary number theory from divisibility through quadratic
reciprocity and Gaussian integers. The interfaces below are the important
dependency nodes; chapter-local proof helpers should not be promoted merely to
make a proof shorter.

## Integer divisibility, Euclidean division, and gcd

`divides_Z(a,b)` means that `b = a*x` for an integer witness. Euclidean
division selects a quotient and bounded remainder, while `gcd_Z(a,b)` selects
the unique nonnegative common divisor divisible by every common divisor.
These are foundational because congruences, prime factorization, and linear
congruences all consume them.

The intended forms are a real `prop` for divisibility, real `prop` relations
for quotient/remainder and gcd specifications, and `have fn ... by exist!` for
the selected quotient and gcd. Encoding either selected value only as a
predicate would lose the source-defined function used downstream. The
remaining restricted-gcd Bézout step should reuse the ordinary checked gcd
identity rather than introduce a second trusted theorem.

## Primes and finite products

`is_prime_Z(p)` states the positive-divisor characterization of a prime.
Finite products are recursive integer-valued functions. Prime factorization
should expose a finite sequence of prime factors whose product is the input,
with uniqueness up to permutation.

The nearest rejected form is an opaque proposition saying merely that
factorization “exists”; the factor sequence and permutation relation matter to
later exponent and divisor arguments. The successor law and prime-divisor
induction over finite products are checked, as is factorization existence by
strong induction. Remaining holes concern permutation uniqueness and maximum
prime-power exponents.

## Congruences and residue-class quotients

`congruent_mod(m,x,y)` is integer divisibility of `x-y` by `m`.
`residue_class_mod(m,x)` is the set of congruent representatives. The ideal
finite quotient carrier is the range of the class map on the standard
representatives `0,...,m-1`. Its Litex form is a set-valued `have fn` whose
defining range is finite. The current grammar does not admit `finite_set` as a
function codomain, so finiteness and cardinality are exposed as theorem-level
laws alongside class addition and multiplication.

The rejected form is an unrestricted set-builder over every subset of `Z`
with no finite presentation. The class and carrier remain real set-valued
functions, not an `abstract_prop`; the carrier's range formula supplies the
finite presentation. They feed
Euler's phi function, linear congruences, residue rings, finite fields, and
Euler's theorem. The open work is the induced operations and their laws, not
the elementary congruence algebra.

## Rings, zero divisors, and fields

A commutative ring is an additive abelian group with associative,
commutative, distributive multiplication; a unitary ring additionally selects
a multiplicative identity. These are distinct `prop` interfaces:
`is_commutative_ring(carrier,add,mul,zero)` and
`is_commutative_unitary_ring(carrier,add,mul,zero,one)`. Requiring a unit in
the basic ring predicate is rejected because the source introduces unitary
rings as a proper refinement. A zero divisor is a nonzero element that
annihilates another nonzero element, also represented by a `prop`.

Fields refine unitary rings by requiring every nonzero element to have a
unique multiplicative inverse. These nodes support the residue-class ring,
the prime-modulus field criterion, and polynomial theory over a field. The
ordinary integer and rational operations are representative use probes; they
need no wrapper objects around the builtin carriers.

## Finite groups, powers, orders, and cyclicity

Groups and subgroups are genuine structural predicates. A group-power relation
must describe finite multiplication for nonnegative exponents and inverse
powers for negative exponents. Element order is the least positive exponent
returning the identity; cyclicity says one element generates the carrier.
The finite cyclic classification must expose the actual power map from
integers (or residue classes) onto the group, with its homomorphism and
bijection laws. A residue-class map that does not mention the group,
operation, or generator is not a translation of that classification.

The nearest rejected form is a circular `generated_subgroup`/power pair that
asserts the desired theorem by definition. These nodes support Lagrange,
Euler, primitive roots, discrete logarithm indices, and finite-field power
congruences. Lagrange's theorem must assume the ambient group laws in addition
to subgroup closure. Euler's theorem is a congruence statement
`congruent_mod(m, a^euler_phi(m), 1)`; raw remainder equality to `1` is not
valid for modulus `1`. Their remaining holes are finite coset counting and
finite subgroup cyclicity.

## Power congruences over prime residue fields

`power_congruence_solvable_mod(p,k,a)` is the existence of an integer solution
to `x^k = a (mod p)`. In Theorem XI.1, `d = gcd(k,p-1)` and
`e*d = p-1` are shared hypotheses for the equivalence between solvability and
`a^e = 1 (mod p)`. The criterion is therefore a `prop` containing an
implication to an iff; it must not put the exponent equation on only one side
or quantify an otherwise unused `e`.

The nearest rejected form is a pair of wrapper predicates in which the
solution side ignores `e` while the reduced-power side requires
`e*d = p-1`. That shape states a false equivalence for arbitrary `e`.
The checked bridge from witness equations to congruence classes feeds Euler's
quadratic-residue criterion and the Legendre symbol. The remaining hole is the
finite cyclic power-map argument.

## Polynomial Euclidean theory

The carrier is a finite-support coefficient function `fn(n N) K`. Polynomial
sum is coefficientwise, while multiplication is represented by a finite
convolution trace at each coefficient. Degree selects the last nonzero
coefficient, and a remainder is zero or has degree below the divisor. The
division, gcd, divisibility, ideal-closure, and principal-generator relations
are consequently typed over `polynomial_ring<K, zero>`.

Representing arbitrary polynomials as untyped `set` values or hiding their
operations in `abstract_prop polynomial_euclidean_data` is rejected. The
concrete carrier and operations are now implemented; the remaining holes are
the Euclidean-division, principal-ideal, and root-count proofs.

## Legendre symbols and quadratic reciprocity

The Legendre symbol is a selected integer in `{-1,0,1}` determined by the
divisible, quadratic-residue, and nonresidue cases. Its ideal Litex form is
`have fn legendre_symbol_Z ... by exist!` backed by a checked exhaustive and
exclusive case proof. Gauss's lemma relates it to the parity of a finite excess
set, and quadratic reciprocity follows from the lattice-count parity identity.

The nearest rejected form is trusting unique existence without proving the
three cases are exhaustive and disjoint. These interfaces depend on finite
residue representatives and the finite-field Euler criterion.

## Gaussian integers

A Gaussian integer is represented concretely by a pair of integers.
Conjugation, addition, multiplication, and norm are real functions; divisibility,
units, associates, and primality are real predicates. Euclidean division should
construct a quotient by rounding rational coordinates and prove the remainder
has smaller norm. Factorization and the two-squares theorem follow.

The nearest rejected form is an opaque Gaussian object with no coordinate
operations. The current concrete carrier is suitable; the remaining holes are
rounding-based Euclidean division, descent, and factorization.
