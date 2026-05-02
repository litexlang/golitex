# Builtin Verification Rules

## Equalities

### Must-Know
Pure numeric goal: reduce both sides with `+ - * / ^` (natural exponents) and compare; no free variables needed.

```litex
2 + 3 * 4 = 14
```

Integer remainder: when `%` has concrete integer operands, the builtin evaluates it like ordinary integer mod.

```litex
4 % 2 = 0
```

Symbolic polynomial identity: normalize equivalent ring expressions (here over `R`) until both sides match.

```litex
forall a, b R:
    (a + b)^2 = a^2 + a*b + b^2 + b*a
```

Rational equality: with valid denominators, prove `a/b = c/d` via cross-multiplication `a*d = b*c` through the rational pipeline.

```litex
2 / 3 = 4 / 6
```

Numeric substitution: after `have ... = k`, the same name may be replaced by `k` when closing an equality.

```litex
have a R = 2
a ^ 2 = 4
```

Named function application: with `have fn`, the checker instantiates the body at the given arguments and compares to the other side.

```litex
have fn f(x R) R = x + 1
f(2) = 3
```

### Absolute Value Rules
If `x` is nonnegative, the builtin can justify `abs(x) = x` after checking `0 <= x`.

```litex
forall x R:
    0 <= x
    =>:
        abs(x) = x
```

If `x` is nonpositive, `abs(x)` matches `-x`; the right-hand side may normalize to `-1 * x` (and similar shapes are accepted).

```litex
forall x R:
    x <= 0
    =>:
        abs(x) = -1 * x
```

Product inside the absolute value splits as `abs(x*y) = abs(x)*abs(y)` as an algebraic identity.

```litex
forall x, y R:
    abs(x * y) = abs(x) * abs(y)
```

For the same even integer exponent on both sides, `x` and `abs(x)` give the same power.

```litex
forall x R:
    x^4 = abs(x)^4
```

From a known equality `abs(x) = 0`, the builtin concludes `x = 0`.

```litex
forall x R:
    abs(x) = 0
    =>:
        x = 0
```

### Power and Algebraic Context Rules
Exponent one: rewrite `a^1` to `a` once the power is well-formed.

```litex
forall a R:
    a^1 = a
```

Exponent addition: for positive-integer exponents `m, n` in `N_pos`, merge `a^(m+n)` with `a^m * a^n` when the law applies.

```litex
forall a R, m, n N_pos:
    a^(m + n) = a^m * a^n
```

Same outer operation on both sides: if each matching argument pair is provably equal (here from `x = y`), the whole expressions are equal.

```litex
forall x, y R:
    x = y
    =>:
        (x + 1) * (x + 1) = (y + 1) * (y + 1)
```

### Logarithm Rules
Inverse of `a^b` at the same base: `log(a, a^b) = b` when the power and `log` are well-defined.

```litex
forall a, b R:
    log(a, a^b) = b
```

Base raised to a power: change-of-base style step `log(a^b, c)` vs `log(a, c) / b` (subject to log domain constraints).

```litex
forall a, b, c R:
    log(a^b, c) = log(a, c) / b
```

Argument raised to a power: pull the exponent out as `b * log(a, x)` on the matching side.

```litex
forall a, x, b R:
    log(a, x^b) = b * log(a, x)
```

Log of a product: split `log(a, x*y)` into the sum of the two logs with the same base.

```litex
forall a, x, y R:
    log(a, x * y) = log(a, x) + log(a, y)
```

Log of a quotient: `log(a, x/y)` becomes the difference of the logs.

```litex
forall a, x, y R:
    log(a, x / y) = log(a, x) - log(a, y)
```

From `a^c = b`, conclude `log(a, b) = c` (log as the inverse of exponentiation, with domain in force).

```litex
forall a, b, c R:
    a^c = b
    =>:
        log(a, b) = c
```

### Sum and Product Rules
Sum of sums: if over the same index range the summand splits pointwise (`f = g + h`), the outer `sum` splits into a sum of two `sum`s.

```litex
sum(1, 3, '(x Z) Z {x + x}) = sum(1, 3, '(x Z) Z {x}) + sum(1, 3, '(x Z) Z {x})
```

Concatenate ranges: `sum(a..b) + sum((b+1)..c)` with the same unary summand equals `sum(a..c)` when endpoints line up.

```litex
sum(1, 3, '(x Z) Z {x + x}) + sum(4, 6, '(x Z) Z {x + x}) = sum(1, 6, '(x Z) Z {x + x})
```

Peel last index off a sum: `sum(s..e,f)` equals `sum(s..e-1,f)` plus the summand at `e` (same unary `f`).

```litex
sum(1, 3, '(x Z) Z {x}) = sum(1, 2, '(x Z) Z {x}) + '(x Z) Z {x}(3)
```

Same peeling rule for finite products, with `*` and the last factor at `e`.

```litex
product(1, 3, '(x Z) Z {x}) = product(1, 2, '(x Z) Z {x}) * '(x Z) Z {x}(3)
```

Partition a closed range: sum over `[start,end]` equals a left-associated chain of shorter sums that tile the interval with gaps `end_i + 1 = start_{i+1}`, same `f` on each piece.

```litex
sum(1, 10, '(x Z) Z {x}) = sum(1, 3, '(x Z) Z {x}) + sum(4, 8, '(x Z) Z {x}) + sum(9, 10, '(x Z) Z {x})
```

Reindex by a constant shift: if both bounds move by the same `k`, reduce to pointwise equality of the summands on the right-hand index interval.

```litex
sum(1, 3, '(x Z) Z {x}) = sum(2, 4, '(x Z) Z {x - 1})
```

Constant summand: if the body does not use the index, the sum over `[s,e]` is `(e-s+1)` times that constant (here laid out arithmetically).

```litex
have c Z
sum(1, 3, '(x Z) Z {c}) = ((3 - 1) + 1) * c
```

### Mod Congruence Rules
Zero remainder: for nonzero modulus `m`, `0 % m` is `0` (includes the dedicated builtin step besides raw evaluation).

```litex
forall m Z:
    m != 0
    =>:
        0 % m = 0
```

Congruence with sum: matching residue equalities for the summands mod `m` imply the same residue for the sums mod `m`.

```litex
forall x1, x2, y1, y2, m Z:
    x1 % m = x2 % m
    y1 % m = y2 % m
    =>:
        (x1 + y1) % m = (x2 + y2) % m
```

Congruence with product: same pattern for products inside `% m` on both sides.

```litex
forall x1, x2, y1, y2, m Z:
    x1 % m = x2 % m
    y1 % m = y2 % m
    =>:
        (x1 * y1) % m = (x2 * y2) % m
```
