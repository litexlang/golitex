# Divisibility, Bezout and congruence systems

## Reused arithmetic and exact domains

An integer multiple witness is the starting point: d divides a when a=k*d
for an integer k. Native `$dvd(a,d)` uses the dividend first and requires
nonzero integer d. This library keeps that convention and domain. Products of
witnesses prove transitivity; distributing multiples proves closure under
integer linear combinations.

`is_congruent_mod(a,b,m)` is `$dvd(a-b,m)` for integer a,b and positive
integer m. Modulus 1, negative operands and zero operands are valid. `%` and
`quot` are native Euclidean remainder and quotient. Congruence is initially a
relation between supplied integers; it does not choose a representative or
construct a quotient ring.

Native gcd is the positive gcd of integer pairs not both zero. Its divisor
laws and positive common-divisor bound establish gcd invariance under adding
an integer multiple of the other argument. They then transport gcd along
congruence. The native Euclidean step gives gcd(a,m)=gcd(m,a%m) for m>0.

## Bezout coefficients exist

The positive-modulus theorem proves

    forall a in Z, m in N+, exists u,v in Z: gcd(a,m)=a*u+m*v.

Strong induction is on m; the induction invariant quantifies over every
integer first operand. At m=1, invariance under adding -a times 1 reduces the
gcd to gcd(0,1)=1, witnessed by coefficients 0,1. At m=d+1, write

    a=(d+1)*q+r, q=quot(a,d+1), r=a%(d+1), 0<=r<d+1.

For r=0 the coefficients 0,1 work. Otherwise r is a positive integer at most d.
Apply the induction hypothesis to the pair (d+1,r), then substitute
r=a-(d+1)*q. If gcd(d+1,r)=(d+1)*u+r*v, the required coefficients are
v and u-q*v. The local invariant remains proof-local.

For general a,b not both zero, split b by sign. Positive b uses the theorem;
negative b uses -b, gcd symmetry and first-argument sign invariance, changing
the second coefficient's sign. If b=0, a is nonzero and gcd(a,0)=abs(a);
coefficients (1,0) or (-1,0) handle its sign. The all-zero pair is not added to
the native gcd domain.

## Modular inverses and integer equations

`is_modular_inverse(a,u,m)` is congruence of a*u and1 modulo positive m.
A supplied identity a*u+m*v=1 gives this inverse relation. Bezout existence
therefore proves inverse existence when gcd(a,m)=1. Conversely, an inverse
provides a*u-1=v*m. The gcd divides both a and m and hence divides
1=a*u+m*(-v); the positive common-divisor bound forces it to be 1. These two
theorems establish the coprime criterion without selecting an inverse value.

A supplied positive Bezout identity can be scaled by an integer multiple of
its right side. Applying it to the actual gcd proves that gcd(a,b) dividing c
is sufficient for a*x+b*y=c when a,b are not both zero. The earlier necessary
divisibility theorem, whose second coefficient b is nonzero, retains its API.
No nonzero assumption is silently dropped from that older interface.

The existing inverse-based cancellation, modular linear equation and inverse
uniqueness theorems now have a proved source of inverse witnesses. Uniqueness
is modulo m. Induction gives compatibility with natural powers and inverse
powers, including exponent zero and the native convention 0^0=1.

## Two-modulus CRT and a canonical output

Assume positive coprime m,n. Bezout coefficients for m,n show that an integer
divisible by both equals k*m*n for an integer k: multiply
1=m*u+n*v by the integer and substitute its two multiple witnesses.

An inverse u of m modulo n gives the actual solution

    x=a+m*u*(b-a).

Then x-a is a multiple of m, and x-b=(m*u-1)*(b-a) is a multiple of n.
Two solutions have a difference divisible by both moduli, so the common
multiple theorem expresses their difference as k*m*n. This is the public
unbounded uniqueness conclusion; it does not assert integer equality.

In the proof, establish that m*n is positive and integer, bind a positive
local modulus to that product, and take x modulo it. Divisibility of the
product by each modulus transports the two congruences to this nonnegative
remainder, which is below m*n. If two bounded solutions differ by k*m*n,
Euclidean-remainder uniqueness gives the same remainder for both and hence
equality. No arbitrary representative choice is needed.

Only after proving unique existence does `have fn ... by exist!` introduce
`chinese_remainder_residue(a,b,m,n)`. Its output is natural, below m*n, and
satisfies the two original congruences. The function requires gcd(m,n)=1;
its domain includes m=1, n=1 and both equal 1. Release the imported function's
definition before using it in a caller's formula or goal.

The dependency spine is:

    integer multiples -> linear combinations and gcd transformations
    -> positive-modulus Bezout -> general Bezout and coprime inverse existence
    -> integer-equation solvability and common-multiple product
    -> CRT existence and unbounded uniqueness
    -> bounded existence and uniqueness -> unique-existence function.

## Evidence and boundaries

`python3 std/number_theory/validation/check.py` passes the 40-statement strict
source, 58-statement full imported consumer and 11 final-only refusal controls.
Generic consumers retain every new theorem's full domains. Concrete consumers
include negative and zero Bezout operands, a zero second coefficient, inverse
existence modulo 1, signed CRT residues, both unit-modulus boundaries, and the
distinction between unbounded and normalized uniqueness.

No trust declaration, axiom, verifier rule or file outside std is introduced.
General noncoprime CRT, more than two congruences, quotient-ring construction,
prime factorization and algorithmic complexity are not established here.
