# Elementary number theory

This strict source library supplies integer congruence with a positive modulus
and 22 named theorems in 24 statements. This includes Euclidean gcd
transformations and modular inverse relations for supplied integer witnesses. It reuses native dividend-first `$dvd(a,d)` directly.
There are no user axioms, trust blocks, new kernel rules or selected values.

## Import and use

Add this to your project's `litex.config`, together with its `[export]` table:

```ini
[import std]
nt = number_theory
```

This complete excerpt is checked independently:

```litex
by def $nt:::is_congruent_mod(17, 2, 5)
release thm nt:::congruence_multiply(17, 2, 17, 2, 5)
$nt:::is_congruent_mod(17 * 17, 2 * 2, 5)
```

The [full example](../../examples/number_theory/congruences/main.lit) includes
negative integers, zero, modulus 1 and noncancellation. The
[generic callers](../../examples/number_theory/congruences/contracts.lit)
exercise every theorem without specializing its parameters.

## Interface and domains

`$is_congruent_mod(a,b,m)` means `$dvd(a-b,m)`: a and b are integers and m
is a positive integer. The modulus domain belongs to the definition itself.
Modulus 1 is allowed; zero, negative and fractional moduli are excluded.

Native `$dvd(a,d)` puts the dividend first and requires a in Z, d in Z*.
Its divisor may be negative and its dividend may be zero. This package adds
no second divisibility predicate and does not define zero-divisor divisibility.

Names below are qualified as `nt:::name` in a caller. Unless stated otherwise,
all letters other than m,n are integers; m,n are positive integers.

| Call | Premises and conclusion |
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
| `congruence_remainder(a,m)` | a is congruent to a%m, reusing native remainder divisibility |
| `congruence_modulus_divisor(a,b,m,n)` | a congruent b modulo n and `$dvd(n,m)` imply congruence modulo m |

Every congruence in a row uses the row's modulus. Congruence does not permit
unconditional cancellation: 2*1 and 2*4 are congruent modulo 6, but 1 and 4 are
not. Cancellation in the new group requires a supplied modular inverse. General
Bezout existence, inverse existence from coprimality, CRT, quotient rings and
primality development remain future work.

## Euclidean transformations and supplied modular inverses

Native gcd(a,b) is positive and excludes only the all-zero pair. The source
uses its divisor laws, positive common-divisor bound and integer multiple
witnesses; no second gcd construction or certificate predicate is added.

`$is_modular_inverse(a,u,m)` means `$is_congruent_mod(a*u,1,m)`, with a,u
integers and m positive. It is a relation about the supplied u. No inverse is
selected, and the package does not assert that every input has one. Modulus1
allows all supplied integers, including zero. Two inverses are congruent
modulo m; they need not be equal as integers.

| New theorem | Premises and result |
| --- | --- |
| `gcd_add_multiple(a,b,k)` | a,k in Z, b in Z*: gcd(a+k*b,b)=gcd(a,b) |
| `congruence_gcd_invariant(a,c,m)` | a congruent c modulo positive m gives gcd(a,m)=gcd(c,m) |
| `gcd_euclidean_step(a,b)` | a integer, b positive: gcd(a,b)=gcd(b,a%b) |
| `linear_equation_necessary_divisibility(a,b,c,x,y)` | b nonzero and a*x+b*y=c imply gcd(a,b) divides c |
| `linear_equation_from_bezout(a,b,u,v,c,d)` | d positive, a*u+b*v=d and d divides c give an integer solution |
| `modular_inverse_from_bezout(a,u,v,m)` | a*u+m*v=1 supplies inverse u |
| `modular_inverse_cancels(a,b,c,u,m)` | Supplied inverse u and a*b congruent a*c imply b congruent c |
| `modular_linear_equation_solution(a,b,u,m)` | Supplied inverse u gives solution x=u*b to a*x congruent b |
| `modular_linear_equation_unique(a,b,u,x,m)` | Supplied inverse and a*x congruent b imply x congruent u*b |
| `modular_inverse_unique(a,u,v,m)` | Both u and v inverse to a imply u congruent v |

The following complete excerpt is checked independently:

```litex
5 * 5 + 12 * (-2) = 1

release thm nt:::modular_inverse_from_bezout(5, 5, -2, 12)

$nt:::is_modular_inverse(5, 5, 12)

by def $nt:::is_congruent_mod(5 * 7, 5 * 19, 12)

release thm nt:::modular_inverse_cancels(5, 7, 19, 5, 12)

$nt:::is_congruent_mod(7, 19, 12)
```

[The new complete caller](../../examples/number_theory/euclidean_inverses/main.lit)
checks the 84/30 Euclidean chain, negative operands, zero first operand,
Diophantine scaling, inverse 5 modulo 12, solutions and uniqueness. Both 5 and 17
invert5 modulo 12. It proves that no integer can invert 2 modulo 6, while the
modulus 1 cases remain valid. [Ten independent generic contracts](../../examples/number_theory/euclidean_inverses/contracts/main.lit)
retain the complete source domains without concrete examples as a prefix.
The original showcase is unchanged; no general Bezout or coprime-existence
proof has been imported implicitly.

## Verification

```bash
target/release/litex -strict -lang en -f std/number_theory/main.lit
python3 examples/number_theory/congruences/check.py
python3 examples/number_theory/euclidean_inverses/check.py
```

The projects verify strict source, generic and concrete callers, the two
README excerpts, 15 original and 20 new final-statement semantic rejections,
actual archive/shared-data installed discovery, and full std/WiX payload and
component references. No Lean or global release certification is implied.
See math_collections.md for the mathematical spine.
