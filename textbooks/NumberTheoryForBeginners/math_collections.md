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
induction over finite products are checked. Remaining holes concern
factorization, permutation uniqueness, and maximum prime-power exponents.

## Congruences and residue-class quotients

`congruent_mod(m,x,y)` is integer divisibility of `x-y` by `m`.
`residue_class_mod(m,x)` is the set of congruent representatives. The ideal
finite quotient interface consists of the finite carrier of all classes,
well-defined class addition and multiplication, and its cardinality.

These must be real set-valued functions and operation specifications, not an
`abstract_prop`. They feed Euler's phi function, linear congruences, residue
rings, finite fields, and Euler's theorem. The open work is the finite quotient
construction and counting, not the elementary congruence algebra.

## Finite groups, powers, orders, and cyclicity

Groups and subgroups are genuine structural predicates. A group-power relation
must describe finite multiplication for nonnegative exponents and inverse
powers for negative exponents. Element order is the least positive exponent
returning the identity; cyclicity says one element generates the carrier.

The nearest rejected form is a circular `generated_subgroup`/power pair that
asserts the desired theorem by definition. These nodes support Lagrange,
Euler, primitive roots, discrete logarithm indices, and finite-field power
congruences. Their remaining holes are finite coset counting and finite
subgroup cyclicity.

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
