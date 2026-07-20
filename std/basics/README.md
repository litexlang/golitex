# `std/basics`

`std/basics` is a small source-level library of shared mathematical
interfaces. Import it with:

```litex
import std basics
```

Use its public names with the explicit `basics::` namespace, for example
`basics::gcd(a, b)` and `by thm basics::bezout_identity(a, b)`.

## Status labels

- **Checked** means that the declaration has a source-level Litex proof.
- **Trusted** means that the declaration is an explicit `trust` background
  interface.
- **Axiom** means that the declaration is explicitly declared as an axiom.

Names beginning with `_` are implementation details, not client API.

## Objects and functions

| Name | Type / role | Status |
| --- | --- | --- |
| `pi` | a positive real constant | Trusted |
| `euler_e` | a positive real constant | Trusted |
| `gcd(a, b)` | positive greatest common divisor of a nonzero integer pair | Checked |

`gcd(a, b)` requires the side condition `a != 0 or b != 0`.

## Predicates

| Name | Meaning |
| --- | --- |
| `is_reduced_fraction(a, b)` | `a : Z`, `b : N_pos`, and their only positive common divisor is `1` |
| `prime(p)` | `p : N_pos`, `p >= 2`, with no divisor in `range(2, p)` |
| `divides(a, b)` | there is `k : Z` with `b = a * k` |

## Theorems

### Rational numbers

| Theorem | Conclusion | Status |
| --- | --- | --- |
| `rational_has_unique_reduced_fraction(q)` | one `a : Z`, `b : N_pos` with `q = a / b` and `is_reduced_fraction(a, b)` | Trusted |
| `rational_has_reduced_fraction(q)` | some `p : Z`, `d : N_pos` with `q = p / d` and `gcd(p, d) = 1` | Checked |

The second theorem is the checked reduced-fraction existence theorem. The first
is a separate, currently trusted unique-normal-form interface.

### Finite sets

| Theorem | Conclusion | Status |
| --- | --- | --- |
| `finite_set_has_bijective_index(s)` | there is `idx : range(0, finite_set_size(s)) -> s` satisfying the kernel predicate `$bijective(range(0, finite_set_size(s)), s, idx)` | Checked |

The module does not define `zero_index`, `zero_index_set`, or a local
bijection predicate. Function properties are kernel vocabulary:
`$injective(A, B, f)`, `$surjective(A, B, f)`, and `$bijective(A, B, f)`, with
`f : fn(x A) B`. This keeps the theorem's public result usable without a
`std/basics`-specific wrapper.

`finite_set_max(S)` and `finite_set_min(S)` are kernel builtins, not names
exported by `std/basics`. They require a finite, nonempty set of real numbers;
they belong to the set and bound every member. Literal calls such as
`finite_set_max({1, 2, 3, 4})` compute directly.

### Divisibility and gcd

| Theorem | Conclusion |
| --- | --- |
| `gcd_positive(a, b)` | `gcd(a, b) $in N_pos` |
| `gcd_divides_left(a, b)` | `gcd(a, b)` divides `a` |
| `gcd_divides_right(a, b)` | `gcd(a, b)` divides `b` |
| `common_divisor_le_gcd(a, b, d)` | a positive common divisor `d` is at most `gcd(a, b)` |
| `gcd_euclidean_base(a)` | `gcd(a, 0) = abs(a)` when `a != 0` |
| `gcd_euclidean_step(a, b)` | `gcd(a, b) = gcd(b, a % abs(b))` when `b != 0` |
| `bezout_identity(a, b)` | there are `x, y : Z` with `gcd(a, b) = x * a + y * b` |
| `gcd_of_prime_is_one_or_prime(a, p)` | for prime `p`, `gcd(a, p)` is `1` or `p` |

Except where a row states a stronger condition, gcd theorems require
`a != 0 or b != 0`.

## Other explicit background interface

| Declaration | Meaning | Status |
| --- | --- | --- |
| `subset_of_finite_set_is_finite(A, B)` | a subset of a finite set is finite | Axiom |

## Minimal use

```litex
import std basics

thm every_rational_has_coprime_integer_fraction:
    ? forall q Q:
        exist p Z, d N_pos st {q = p / d, basics::gcd(p, d) = 1}
    by thm basics::rational_has_reduced_fraction(q)
```

The implementation and the full theorem statements are in
[`main.lit`](main.lit).
