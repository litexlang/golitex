# Builtin Verification Rules

The checker can close some **atomic** goals without a user `prove` step, using built-in algebraic and logical steps. **Equalities** are handled mainly by evaluation, normalization, and laws in the sections below. **Comparisons** (`<`, `<=`, `>`, `>=`, and related negations), **membership** in standard number sets, **subset** claims, **non-equality**, and several **type** predicates are handled by a different style of reasoning: facts about signs and nonnegative expressions, monotonicity of `+`, `-`, `*`, `/` under the usual side conditions for real variables, properties of `abs`, and—when both sides are explicit fractions with nonzero denominators—clearing denominators to compare numerators.

## Equalities

### Must-Know
Pure numeric goal: reduce both sides with `+ - * / ^` (natural exponents) and compare; no free variables needed.

```litex
2 + 3 * 4 = 14
```

Integer remainder: when `%` has concrete integer operands, evaluation follows ordinary integer remainder.

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

### Parametric families (`family`)

A parameterized `family`…`=` definition expands to the corresponding `fn(...)` function space when you instantiate it (for example with `\name(R)`). Equalities between an instantiated family and that expanded `fn` can be closed once parameters match.

```litex
prove:
    family p(a set) = fn(x a) a
    \p(R) = fn(x R) R
```

### Anonymous function application

Applying an anonymous function head substitutes the actual arguments into its body; the result is compared like any other equality.

```litex
'R(x){x + 1}(2) = 3
```

### Absolute Value Rules
If `x` is nonnegative, the checker can justify `abs(x) = x` after checking `0 <= x`.

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
        abs(x) = -x
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

From a known equality `abs(x) = 0`, the checker concludes `x = 0`.

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

**Structural equality:** the same “matching head, equal arguments” principle extends to other composite heads (matrices, `max` / `min`, binary set operators, etc.) whenever both sides are the same kind of expression and corresponding sub-expressions are equal.

### Zero from subtraction and from powers

A literal `0` opposite a difference `x - y` closes when `x` and `y` are known equal (either side may carry the subtraction).

```litex
prove:
    have x R = 5
    x - x = 0
```

If one side is `0` and the other is `a^n`, with **`n` a positive integer literal** and `a` in question, the goal reduces to `a = 0`.

```litex
prove:
    forall a R:
        a = 0
        =>:
            a ^ 3 = 0
```

### Logarithm Rules

Inverse of `a^b` at the same base: `log(a, a^b) = b` when the power and `log` are well-defined.

```litex
forall a, b R_pos:
    a != 1
    =>:
        log(a, a^b) = b
```

Base raised to a power: change-of-base style step `log(a^b, c)` vs `log(a, c) / b` (subject to log domain constraints).

```litex
forall a, b, c R_pos:
    a != 1
    a^b != 1
    =>:
        log(a^b, c) = log(a, c) / b
```

Argument raised to a power: pull the exponent out as `b * log(a, x)` on the matching side.

```litex
forall a, x, b R_pos:
    a != 1
    =>:
        log(a, x^b) = b * log(a, x)
```

Log of a product: split `log(a, x*y)` into the sum of the two logs with the same base.

```litex
forall a, x, y R_pos:
    a != 1
    =>:
        log(a, x * y) = log(a, x) + log(a, y)
```

Log of a quotient: `log(a, x/y)` becomes the difference of the logs.

```litex
forall a, x, y R_pos:
    a != 1
    =>:
        log(a, x / y) = log(a, x) - log(a, y)
```

From `a^c = b`, conclude `log(a, b) = c` (log as the inverse of exponentiation, with `a`, `b` positive and `a != 1`).

```litex
forall a, b R_pos, c R:
    a != 1
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

The same “tiling” step exists for **products**: multiply the `product` over each sub-interval, with the same unary factor on each piece.

```litex
product(1, 10, '(x Z) Z {x}) = product(1, 3, '(x Z) Z {x}) * product(4, 8, '(x Z) Z {x}) * product(9, 10, '(x Z) Z {x})
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
Zero remainder: for nonzero modulus `m`, `0 % m` is `0` (this also agrees with purely numeric evaluation of `%`).

```litex
forall m Z:
    m != 0
    =>:
        0 % m = 0
```

Congruence with sum: matching residue equalities for the summands mod `m` imply the same residue for the sums mod `m`.

```litex
forall x1, x2, y1, y2 Z, m N_pos:
    x1 % m = x2 % m
    y1 % m = y2 % m
    =>:
        (x1 + y1) % m = (x1 % m + y1 % m) % m = (x2 % m + y2 % m) % m = (x2 + y2) % m
```

Congruence with difference: the same idea applies to differences inside `% m`.

```litex
forall x1, x2, y1, y2, m Z:
    m != 0
    x1 % m = x2 % m
    y1 % m = y2 % m
    =>:
        (x1 - y1) % m = (x2 - y2) % m
```

Congruence with product: same pattern for products inside `% m` on both sides.

```litex
forall x1, x2, y1, y2, m Z:
    m != 0
    x1 % m = x2 % m
    y1 % m = y2 % m
    =>:
        (x1 * y1) % m = (x2 * y2) % m
```

Nested modulus with the **same** `m`: taking `% m` twice is redundant; `(x % m) % m` matches `x % m`.

```litex
prove:
    (5 % 7) % 7 = 5 % 7
```

When one side has an extra outer `% m` on part of the other (after associating nested remainders), the checker may **peel** that outer layer and reduce to a simpler residue equality (often so the sum/product congruence rules apply).

## Order and comparison

Ordering goals (`<`, `<=`, `>`, `>=`, and related `not` forms) are **not** handled by the same steps as equalities above.

### Literals and reflexivity

Concrete numeric inequalities after evaluation, and reflexivity `a <= a`.

```litex
1 < 2
```

```litex
2 <= 2
```

### Fractions (clearing denominators)

When both sides are written as fractions with **nonzero** evaluated denominators, the checker may compare by cross-multiplying numerators (equivalent to a common denominator), in line with the usual order of rationals.

```litex
prove:
    1 / 2 < 3 / 4
```

### Bounds from `N` and `N_pos`

```litex
forall n N_pos:
    1 <= n
```

```litex
forall n N:
    0 <= n
```

From `n $in N` and `n != 0`, a nonnegative integer not equal to zero is at least `1` (equivalently `N_pos` as a subset of `N` characterized by `n != 0`).

```litex
forall x N:
    x != 0
    =>:
        1 <= x
```

Conversely, from `n $in N` and `1 <= n`, conclude `n != 0`.

```litex
forall x N:
    1 <= x
    =>:
        x != 0
```

### Nonnegative sums (long chains)

From `0 <=` on each summand, close `0 <=` on a left-associated sum (works for more than two terms).

```litex
forall a, b R:
    0 <= a
    0 <= b
    =>:
        0 <= a + b
```

```litex
let a, b, c R:
    0 <= a
    0 <= b
    0 <= c

0 <= a + b + c
```

### Positive / strict addition

```litex
forall a, b R:
    0 < a
    0 <= b
    =>:
        0 < a + b
```

```litex
forall a, b, c R:
    a < b
    0 <= c
    =>:
        a < b + c
```

### Nonnegative products, quotients, and powers

Typical `0 <= …` / `0 < …` steps for `*`, `/`, and `^` when variables range over `R`, assuming the expressions are well-defined and the usual sign constraints hold (nonnegative factors where required, positive denominator for strict order through division, etc.).

```litex
0 <= 3 * 2
```

```litex
0 <= 3 / 2
```

```litex
0 <= (-2) ^ 2
```

```litex
forall a R:
    0 <= a ^ 2
```

```litex
0 < 2 ^ 3
```

### Weak order: combine inequalities (algebra)

```litex
forall a, b, c, d R:
    a <= b
    c <= d
    =>:
        a + c <= b + d
```

```litex
forall a, b, c, d R:
    a <= b
    c <= d
    =>:
        a - d <= b - c
```

```litex
forall a, b R:
    0 <= a
    1 <= b
    =>:
        a <= b * a
```

```litex
prove:
    have k R = 2
    have a R = 1
    have b R = 3
    0 <= k
    a <= b
    k * a <= k * b
```

```litex
prove:
    have a R = 2
    have b R = 4
    have c R = 3
    0 < c
    a < b
    a / c < b / c
```

### Sign flips with `(-1) *`

```litex
forall x R:
    x <= 0
    =>:
        0 <= -1 * x
```

### Absolute value versus order

```litex
forall x R:
    x <= abs(x)
```

```litex
forall x R:
    -x <= abs(x)
```

```litex
forall x R:
    0 <= abs(x)
```

```litex
forall x, b R:
    x <= b
    -x <= b
    =>:
        abs(x) <= b
```

```litex
forall x, y R:
    abs(x + y) <= abs(x) + abs(y)
```

```litex
forall x, y R:
    abs(x) - abs(y) <= abs(x + y)
```

## Membership (standard number sets)

Literals (and many arithmetic combinations of literals) can be checked against `R`, `Q`, `N`, `N_pos`, and related standard sets.

```litex
1 $in N_pos
```

```litex
1 + 1 $in N
```

### Non-membership

Negated membership `not x $in S` for a standard set `S` is checked for concrete numeric `x` by comparing membership in the same way, when evaluation resolves `x` to a normalized decimal.

```litex
prove:
    not (-1) $in N
```

### `max` / `min` in a cone

If `max(a,b)` or `min(a,b)` is asserted inside a standard **one-sided** number cone (`R_pos`, `R_neg`, `N`, `N_pos`, etc.), the checker may close the goal when **both** operands are already known to lie in that same cone.

```litex
prove:
    max(2, 3) $in R_pos
```

### Finite `sum` / `product` in `R`

A finite `sum` or `product` over an integer range is treated as a real once the indexed expression is well-defined under the usual rules.

```litex
prove:
    sum(1, 3, '(x Z) Z {x}) $in R
```

## Inequality (not equal)

Disequalities such as `!=` can close when ordering or numeric facts already rule out equality.

```litex
2 != 3
```

## Set inclusion

Subset goals are equivalent to universal membership: every element of the left set lies in the right set.

```litex
{1} $subset {1, 2}
```

Claims involving superset and negated subset/superset can be related the same way; when a direct subset statement is clumsy, spell out the universal membership as in a manual proof.

## Other type predicates

The checker treats syntactic set forms as sets.

```litex
$is_set({1, 2})
```

### Non-emptiness

Nonempty **enumerated** sets, **standard** sets (such as `R`), integer **closed ranges** when the endpoints satisfy `start <= end`, **Cartesian products** when every factor is nonempty, nonempty **function spaces** `fn(...)` when the declared value set is nonempty, and similar shapes.

```litex
$is_nonempty_set({1})
```

```litex
prove:
    $is_nonempty_set(closed_range(0, 2))
```

```litex
prove:
    $is_nonempty_set(cart(R_pos, R_pos))
```

A **negated** non-emptiness claim can be discharged for an **empty** enumeration `{}`.

```litex
prove:
    not $is_nonempty_set({})
```

Standard finite-set syntax.

```litex
$is_finite_set({1, 2})
```

Tuple and Cartesian-product shapes are recognized structurally.

```litex
$is_tuple((2, 3))
```

```litex
$is_cart(cart(R, Q))
```

## Function equality on a set (`$fn_eq_in`)

Pointwise equality on a domain: `$fn_eq_in(f, g, S)` means `forall x in S, f(x) = g(x)`. The checker reduces this to that quantified statement; you often expose the pointwise equalities first (including by unfolding `have fn` definitions).

```litex
have fn f(x R) R = x
have fn g(x R) R = x

forall x R:
    f(x) = x = g(x)

$fn_eq_in(f, g, R)
```

Anonymous heads can be compared the same way when they denote the same map on `S`.

```litex
$fn_eq_in('R(x){x}, 'R(y){y}, R)
```

## Function equality from the function type (`$fn_eq`)

`$fn_eq(f, g)` is for values whose **function type** is given by the same `fn(...)` / `have fn` specification on both sides. After checking that the type data matches in both directions (parameters, domain conditions, declared value set), the goal is reduced to a parameterized `forall` proof that `f` and `g` agree on every argument tuple—similar in spirit to `$fn_eq_in`, but driven by the declared `fn` type rather than an explicit set `S`.

```litex
$fn_eq('R(x){x}, 'R(y){y})
```

```litex
have fn f(x R) R = x
have fn g(x R) R = x
forall x R:
    f(x) = x = g(x)
$fn_eq(f, g)
```

Two **function-set** values written with the same `fn`…parameter list and body-shaped data can be proved equal when each side implies the other as a type (matching parameters, domain facts, and value set).
