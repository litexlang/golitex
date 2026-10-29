# Elementary number theory

This strict source library supplies integer divisibility, congruence, Euclidean
transformations, Bezout existence, coprime modular inverses and the two-modulus
Chinese remainder theorem. It contains 37 named theorems and one function in
40 source statements. It adds no user axioms, trust blocks or native rules.

## Import and use

Add the following to the caller's `litex.config`, with its own `[export]` table:

```ini
[import std]
NumberTheory = number_theory
[alias]
nt = NumberTheory::main
```

The following calls occur in the [checked consumer](validation/main.lit):

```litex
release obj def nt::chinese_remainder_residue

by def $nt::is_congruent_mod(8,2,3)

by def $nt::is_congruent_mod(8,3,5)

release thm nt::chinese_remainder_residue_of_solution(2,3,3,5,8)

nt::chinese_remainder_residue(2,3,3,5)=8
```

The function comes from proved unique existence. Release its definition before
using the imported function in a formula or generic goal. Its specification is
available at every legal application; it has no expression body to unfold.

## Domains and existing arithmetic

`$is_congruent_mod(a,b,m)` means native `$dvd(a-b,m)`: a,b are integers and
m is a positive integer. Native divisibility is **dividend first**; `$dvd(a,d)`
requires a in Z and d in Z*. Negative divisors are allowed by the native
predicate. This library does not extend divisibility to a zero divisor.

Native `gcd(a,b)` is positive and defined on integer pairs not both zero.
The general Bezout and Diophantine existence theorems keep this exact domain.
Euclidean `%` and `quot` remain the native remainder and quotient. There is no
second gcd construction or certificate predicate.

`$is_modular_inverse(a,u,m)` means `$is_congruent_mod(a*u,1,m)`. It is a
relation about the supplied integer u. Both existence from `gcd(a,m)=1` and
necessity of that condition are proved. No inverse function is selected.
Modulus 1 is legitimate, including a=0 and u=0.

## Divisibility and congruence

Use the prefix `nt::` on the following names. Unless specified otherwise,
a,b,c,d,t,x,y,u,v are integers and m,n are positive integers.

| Theorem | Premises and result |
| --- | --- |
| `divisibility_transitive(a,b,d)` | b,d in Z*, d divides b and b divides a imply d divides a |
| `divisibility_linear_combination(a,b,x,y,d)` | d in Z*, d divides a,b implies d divides a*x+b*y |
| `congruence_reflexive(a,m)` | a is congruent to itself |
| `congruence_symmetric(a,b,m)` | a congruent b implies b congruent a |
| `congruence_transitive(a,b,c,m)` | a congruent b and b congruent c imply a congruent c |
| `congruence_add(a,b,c,d,m)` | a congruent b and c congruent d imply a+c congruent b+d |
| `congruence_subtract(a,b,c,d,m)` | Same premises imply a-c congruent b-d |
| `congruence_multiply(a,b,c,d,m)` | Same premises imply a*c congruent b*d |
| `congruence_scale(a,b,t,m)` | a congruent b implies t*a congruent t*b |
| `congruence_negate(a,b,m)` | a congruent b implies -a congruent -b |
| `congruence_remainder(a,m)` | a is congruent to a%m |
| `congruence_modulus_divisor(a,b,m,n)` | Congruence modulo n and `$dvd(n,m)` imply congruence modulo m |
| `congruence_power(a,b,m,n)` | a congruent b implies congruence of natural powers n |
| `congruence_power_remainder(a,m,n)` | `a^n` is congruent to `(a%m)^n` for natural n |

Every congruence in a row uses the stated modulus. The power theorems allow
negative or zero integer bases and exponent zero, using Litex's `0^0=1`
convention. Congruence does not permit unconditional cancellation: 2*1 and
2*4 are congruent modulo 6, while 1 and 4 are not.

## Euclidean steps and supplied witnesses

| Theorem | Premises and result |
| --- | --- |
| `gcd_add_multiple(a,b,k)` | b in Z*, k in Z: gcd(a+k*b,b)=gcd(a,b) |
| `congruence_gcd_invariant(a,c,m)` | a congruent c implies gcd(a,m)=gcd(c,m) |
| `gcd_euclidean_step(a,b)` | b positive: gcd(a,b)=gcd(b,a%b) |
| `linear_equation_necessary_divisibility(a,b,c,x,y)` | b nonzero and a*x+b*y=c imply gcd(a,b) divides c |
| `linear_equation_from_bezout(a,b,u,v,c,d)` | d positive, a*u+b*v=d and d divides c give an integer solution |
| `modular_inverse_from_bezout(a,u,v,m)` | a*u+m*v=1 supplies inverse u |
| `modular_inverse_cancels(a,b,c,u,m)` | Inverse u and a*b congruent a*c imply b congruent c |
| `modular_linear_equation_solution(a,b,u,m)` | Inverse u gives solution u*b to a*x congruent b |
| `modular_linear_equation_unique(a,b,u,x,m)` | Inverse u and a*x congruent b imply x congruent u*b |
| `modular_inverse_unique(a,u,v,m)` | Both u and v inverse to a imply u congruent v |
| `modular_inverse_power(a,u,m,n)` | A supplied inverse remains an inverse after both values are raised to natural n |

The previous supplied-witness interfaces remain available. Inverse uniqueness
is congruence, not integer equality.

## Existence and the Chinese remainder theorem

| Theorem | Premises and result |
| --- | --- |
| `bezout_positive_modulus(a,m)` | Integer coefficients u,v exist with gcd(a,m)=a*u+m*v |
| `bezout_identity(a,b)` | a,b not both zero: coefficients exist with gcd(a,b)=a*u+b*v |
| `coprime_modular_inverse_exists(a,m)` | gcd(a,m)=1 gives an integer inverse |
| `modular_inverse_implies_coprime(a,u,m)` | A supplied inverse implies gcd(a,m)=1 |
| `linear_equation_from_gcd(a,b,c)` | a,b not both zero and gcd(a,b) divides c give integer x,y with a*x+b*y=c |
| `coprime_common_multiple(a,m,n)` | Coprime m,n both divide a: integer k exists with a=k*m*n |
| `chinese_remainder_exists(a,b,m,n)` | Coprime m,n: integer x exists congruent to a modulo m and b modulo n |
| `chinese_remainder_unique(a,b,x,y,m,n)` | Two such solutions differ by k*m*n for some integer k |
| `chinese_remainder_bounded_exists(a,b,m,n)` | Coprime m,n: such an r exists in N with r<m*n |
| `chinese_remainder_bounded_unique(a,b,m,n,x,y)` | Two such natural solutions below m*n are equal |
| `chinese_remainder_unique_residue(a,b,m,n)` | Exactly one such r in N lies below m*n |
| `chinese_remainder_residue_of_solution(a,b,m,n,r)` | A natural solution r<m*n equals the standard residue function |

`chinese_remainder_residue(a,b,m,n)` has integer a,b, positive integer m,n,
the domain condition `gcd(m,n)=1`, and natural output r. Its specification is
`r<m*n`, congruence to a modulo m and congruence to b modulo n. There is no
modulus-product parameter or extra witness supplied by the caller.

The consumer checks the value 8 for residues 2 modulo 3 and 3 modulo 5; value 2
for residues -1 modulo 3 and 2 modulo 5; a unit first modulus; and both moduli
1, whose standard residue is 0. Arbitrary integer residues and positive moduli
1 are retained. The unbounded solutions 8 and 23 illustrate uniqueness only
up to a multiple of 15.

This is the two-modulus coprime CRT. A compatible noncoprime pair is outside
the selected function's domain. General noncoprime CRT, arbitrary finite
systems, quotient rings and prime factorization remain future work. Bezout
coefficients exist but no particular coefficient algorithm or complexity bound
is claimed.

## Verification

```bash
python3 std/number_theory/validation/check.py
```

The source-owned checker verifies 40 strict source statements, 58 imported
consumer statements (including full-domain calls for all 12 new theorems), and
11 final-statement refusals in a fresh persistent strict Session. These cover
all-zero Bezout inputs, missing coprimality/divisibility, zero and fractional
moduli, function-domain rejection, incorrect integer uniqueness and incorrect
or out-of-range standard residues. Each refusal requires an accepted prefix.

The existing external examples under `examples/number_theory/` provide older
congruence, power and supplied-inverse demonstrations. No installer, Lean or
repository-wide release gate is claimed for this std-only batch. See
[the mathematical spine](math_collections.md) for the proof dependencies.
