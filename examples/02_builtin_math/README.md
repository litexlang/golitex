# Builtin Math

Examples for builtin arithmetic, order, intervals, finite sets, powers, absolute value, logs, sums, products, and modular arithmetic.

Each Litex block below is checked independently by `cargo test run_examples -- --nocapture`.
The `Category` and `System surface` fields say what part of Litex the example is meant to exercise.

## 1. `abs`

- Category: `builtin rule`
- System surface: `absolute value`
- Purpose: Shows builtin absolute-value inequalities and equalities.

```litex
forall a R:
    a >= 0
    =>:
        abs(a) = a

forall a R:
    a <= 0
    =>:
        abs(a) = -a

forall a R:
    0 <= abs(a)
    abs(a) = a or abs(a) = -a

forall a R:
    abs(a) = 0
    =>:
        a = 0

forall x, y R:
    abs(x * y) = abs(x) * abs(y)

forall x R:
    x <= abs(x)
    -x <= abs(x)

forall x, b R:
    x <= b
    -x <= b
    =>:
        abs(x) <= b

forall x, b R:
    x < b
    -x < b
    =>:
        abs(x) < b

forall x, y R:
    abs(x) <= abs(y)
    =>:
        -abs(y) <= x <= abs(y)

forall x, y R:
    abs(x) < abs(y)
    =>:
        -abs(y) < x < abs(y)

forall x, y R:
    abs(x) <= abs(y)
    0 <= y
    =>:
        -y <= x <= y

forall x, y R:
    abs(x) <= abs(y)
    y <= 0
    =>:
        y <= x <= -y

forall x, y R:
    abs(x + y) <= abs(x) + abs(y)
    abs(x - y) <= abs(x) + abs(y)

forall x, y R:
    abs(x) - abs(y) <= abs(x + y)
    abs(x) - abs(y) <= abs(x - y)

forall x R:
    x ^ 2 = abs(x) ^ 2
    x ^ 4 = abs(x) ^ 4

forall a, b R:
    0 <= a <= b
    =>:
        abs(a) <= abs(b)

forall a, b R, k N_pos:
    k % 2 = 0
    abs(a) <= abs(b)
    =>:
        a^k <= b^k
```

## 2. `basic_operator`

- Category: `builtin rule`
- System surface: `basic operators`
- Purpose: Shows arithmetic operator typing and simplification.

```litex
+ = +
* = *
/ = /
% = %
^ = ^
+ $in fn(a, b R) R
- $in fn(a, b R) R
* $in fn(a, b R) R
/ $in fn(a R, b R: b != 0) R
% $in fn(a Z, b Z: b != 0) Z
^ $in fn(a, b R: a $in R_pos or a = 0 and b $in R_pos or a $in R_nz and b $in Z or b $in N) R
```

## 3. `builtin_rules`

- Category: `builtin rule`
- System surface: `order and arithmetic rules`
- Purpose: Shows common builtin arithmetic/order inference rules.

```litex
forall a, b R_pos:
    1 <= a
    =>:
        b <= a * b

forall a, b R_pos:
    1 < a
    =>:
        b < a * b

forall a, b R:
    a > 0
    b > 1
    =>:
        a / b < a

forall a, b, k R:
    0 <= k
    a <= b
    =>:
        k * a <= k * b

forall a, b, k R:
    0 < k
    a < b
    =>:
        k * a < k * b

forall a, b, c, d R:
    a < b
    c <= d
    =>:
        a - d < b - c

forall x, a, b R:
    x < b
    0 <= a
    =>:
        x - a < b

forall x, a, b R:
    x <= b
    0 < a
    =>:
        x - a < b

forall a, b, c R:
    a + c < b
    =>:
        a < b - c

forall a R:
    0 < a
    =>:
        a != 0
```

## 4. `builtin_sqrt`

- Category: `builtin rule`
- System surface: `sqrt`
- Purpose: Shows square-root typing and identities.

```litex
sqrt(4) = sqrt(4)
sqrt(0) = 0
sqrt(1) = 1
sqrt(4) = 2
sqrt(452) = sqrt(4 * 113)
sqrt(452) = sqrt(4 * 113) = sqrt(4) * sqrt(113) = 2 * sqrt(113)

forall x R:
    x >= 0
    =>:
        (sqrt(x))^2 = x

forall x R:
    x > 0
    =>:
        sqrt(x) > 0

forall x R:
    x >= 0
    =>:
        sqrt(x) >= 0

forall x, a, b R:
    x >= 0
    a >= 0
    b >= 0
    x = a * b
    =>:
        sqrt(x) = sqrt(a) * sqrt(b)

forall x, a, b R:
    x >= 0
    a >= 0
    b > 0
    x = a / b
    =>:
        sqrt(x) = sqrt(a) / sqrt(b)

forall a, b R:
    a >= 0
    b >= 0
    a <= b
    =>:
        sqrt(a) <= sqrt(b)

forall a, b R:
    a >= 0
    b >= 0
    a < b
    =>:
        sqrt(a) < sqrt(b)
```

## 5. `closed_range`

- Category: `obj`
- System surface: `closed_range`
- Purpose: Shows closed integer range objects.

```litex
have a 1...3

by closed_range as cases: a $in 1...3

a = 1 or a = 2 or a = 3
```

## 6. `closed_range_and_range`

- Category: `obj`
- System surface: `range and closed_range`
- Purpose: Shows interaction between half-open and closed ranges.

```litex
forall i Z:
    1 < i < 5
    =>:
        i $in range(2, 5)
        i $in 2...4

forall i Z:
    1 <= i < 5
    =>:
        i $in range(1, 5)
        i $in 1...4

forall i Z:
    1 <= i <= 5
    =>:
        i $in range(1, 6)
        i $in 1...5

forall i Z:
    1 < i <= 5
    =>:
        i $in range(2, 6)
        i $in 2...5

count(1...5) =  5
count(range(1, 5)) = 4
```

## 7. `comparison`

- Category: `builtin rule`
- System surface: `comparison`
- Purpose: Shows comparison facts and chained inequalities.

```litex
know:
    forall a, b, c R:
        0 < c
        =>:
            a * c <= b
        <=>:
            a <= b / c

claim:
    prove:
        forall a, b, c, d R:
            2 * a <= 3 * b
            1 <= a
            d = 2
            =>:
                d + a <= 5 * b
    d = 2 * 1 <= 2 * a
    a = (2*a)/2 <= (3*b)/2 = 1.5 * b
    0 <= (2/3)* a = (2 * a)/3 <= (3 * b)/3 = b
    d + a <= 2 * a + a <= 3 * b + a <= 3 * b +1.5*b = 4.5*b <= 5 * b

prove:
    forall x N:
        x != 0
        =>:
            1 <= x
    forall x N:
        1 <= x
        =>:
            x != 0

forall x, y R:
    =>:
        x != 0 or y != 0
    <=>:
        x^2 + y^2 != 0

forall x, y R:
    =>:
        x*x + y*y != 0
    <=>:
        x != 0 or y != 0


forall a, b R:
    a <= 0
    b >= 0
    =>:
        a * b <= 0

forall a, b R:
    a >= 0
    b <= 0
    =>:
        a * b <= 0

forall a, b R:
    a >= 0
    b >= 0
    =>:
        a * b >= 0

forall a, b R:
    a <= 0
    b <= 0
    =>:
        a * b >= 0

forall a, b R:
    a < 0
    b > 0
    =>:
        a * b < 0

forall a, b R:
    a > 0
    b > 0
    =>:
        a * b > 0

forall a, b R:
    a < b
    =>:
        a^3 < b^3
        b^5 > a^5

prove:
    forall t R_pos:
        t^2 < 4^2
        =>:
            t < 4

    forall t R_pos:
        t^3 < 4^3
        =>:
            t < 4

    forall t R_pos:
        t^4 < 4^4
        =>:
            t < 4

    forall t R_pos:
        t^5 < 4^5
        =>:
            t < 4

claim:
    prove:
        forall t R_pos:
            t^6 < 4^6
            =>:
                t < 4
    by thm pos_pow_strict_order_reflects(t, 4, 6)
```

## 8. `comparison3`

- Category: `builtin rule`
- System surface: `comparison`
- Purpose: Shows additional comparison simplification cases.

```litex
know:
    forall a R:
        0 <= a
        =>:
            -a <= 0

    forall a R:
        a <= 0
        =>:
            0 <= -a

know:
    forall a, b R:
        a <= b
        =>:
            0 <= b - a

know:
    forall a, b, c, d R:
        0 <= a < c
        0 <= b < d
        =>:
            a * b < c * d

    forall a, b, c, d R:
        0 <= a < c
        0 <= b < d
        =>:
            a * b < c * d

claim:
    prove:
        forall x, y, epsilon R:
            0 < epsilon
            epsilon <= 1
            abs(x) < epsilon
            abs(y) < epsilon
            =>:
                abs(x * y) < epsilon
    0 <= abs(x) < epsilon
    0 <= abs(y) < epsilon
    abs(x * y) = abs(x) * abs(y) < epsilon * epsilon <= epsilon * 1 = epsilon
```

## 9. `comparison4`

- Category: `builtin rule`
- System surface: `comparison`
- Purpose: Shows comparison over mixed arithmetic forms.

```litex

claim:
    prove:
        forall a, b R:
            0 <= a
            a <= 1
            0 <= b
            b <= 1
            =>:
                a * b <= 1
    0 <= 1 - a
    0 <= (1 - a) * b = b - a * b
    a * b <= b <= 1
```

## 10. `comparison5`

- Category: `builtin rule`
- System surface: `comparison`
- Purpose: Shows comparison facts that need local side conditions.

```litex
let a, b, c, d, e, f, g R:
    0 <= a
    0 <= b
    0 <= c
    0 <= d
    0 <= e
    0 <= f
    0 <= g

0 <= a + b + c + d + e + f + g

let h, i, j, k, l, m, n, o R

0 <= a + b + (h + i)^2 + (j + k)^4 + (l + m)^6 + (n + o)^8

0 <= a^3 + b^3 + c^3 + d^3 + e^3 + f^3 + g^3
```

## 11. `divide`

- Category: `builtin rule`
- System surface: `division`
- Purpose: Shows division and reciprocal simplification.

```litex
forall a, b, c R_nz:
    a / (b / c) = a * c / b
    (a / b) / c = a / (b * c)

forall u R:
    u = 1 / (7 / 3)
    =>:
        u = 1 / (7 / 3) = 3 / 7
        7 * u = 3

forall u R:
    u = (-8 / 33) / (-8)
    =>:
        u = (-8 / 33) / (-8) = 1 / 33

forall u, v, w R:
    w != 0
    u = v / w
    =>:
        u * w = v
```

## 12. `finite_set`

- Category: `obj`
- System surface: `finite set`
- Purpose: Shows finite-set literals, membership, and count facts.

```litex
$is_finite_set({1, 2})
count({1, 2, 3}) = 3
count(cart({1, 2}, {3, 4, 5})) = count({1, 2}) * count({3, 4, 5})

$is_finite_set(union({1, 2}, {2, 3}))
$is_finite_set(intersect({1, 2}, {2, 3}))
$is_finite_set(set_minus({1, 2}, {2, 3}))
$is_finite_set(set_diff({1, 2}, {2, 3}))

count(intersect({1, 2}, {2, 3})) <= count({1, 2})
count(intersect({1, 2}, {2, 3})) <= count({2, 3})
count(set_minus({1, 2}, {2, 3})) <= count({1, 2})
count(union({1, 2}, {2, 3})) <= count({1, 2}) + count({2, 3})
count(set_diff({1, 2}, {2, 3})) <= count({1, 2}) + count({2, 3})

count(union({1, 2}, {2, 3})) = count({1, 2}) + count({2, 3}) - count(intersect({1, 2}, {2, 3}))
count(set_minus({1, 2}, {2, 3})) = count({1, 2}) - count(intersect({1, 2}, {2, 3}))
count(set_diff({1, 2}, {2, 3})) = count(set_minus({1, 2}, {2, 3})) + count(set_minus({2, 3}, {1, 2}))

claim:
    prove:
        forall X, Y set:
            $is_finite_set(X)
            $is_finite_set(Y)
            =>:
                count(cart(X, Y)) = count(X) * count(Y)
    count(cart(X, Y)) = count(X) * count(Y)
```

## 13. `interval`

- Category: `obj`
- System surface: `interval`
- Purpose: Shows interval objects and interval membership.

```litex
# real interval sanity checks
have a oo(0, 1)
a $in R
0 < a
a < 1

have b  oc(0, 1)
0 < b
b <= 1

have c co(0, 1)
0 <= c
c < 1

have d cc(0, 1)
0 <= d
d <= 1

have e info(1)
e $in R
e < 1

have f infc(1)
f $in R
f <= 1

have g oinf(0)
g $in R
0 < g

have h cinf(0)
h $in R
0 <= h

have x R
know:
    0 <= x
x $in cinf(0)

prove:
    $is_nonempty_set(cc(0, 0))

prove:
    $is_nonempty_set(oo(0, 1))

prove:
    $is_nonempty_set(info(1))

prove:
    $is_nonempty_set(infc(1))

prove:
    $is_nonempty_set(oinf(0))

prove:
    $is_nonempty_set(cinf(0))
```

## 14. `log`

- Category: `builtin rule`
- System surface: `log`
- Purpose: Shows logarithm facts and monotonicity-style builtin support.

```litex
# Current builtin logarithm support.

log(2, 8) = 3
log(10, 100) = 2
log(3, 1) = 0
log(5, 5) = 1

forall a R_pos, b R:
    a != 1
    =>:
        log(a, a^b) = b

forall a, b R_pos:
    a != 1
    =>:
        a ^ log(a, b) = b
        log(a, a) = 1
        log(a, 1) = 0

forall a, b, c R_pos:
    a != 1
    a^b != 1
    =>:
        log(a^b, c) = log(a, c) / b

forall a, x, b R_pos:
    a != 1
    =>:
        log(a, x^b) = b * log(a, x)

forall a, x, y R_pos:
    a != 1
    =>:
        log(a, x * y) = log(a, x) + log(a, y)
        log(a, x / y) = log(a, x) - log(a, y)

forall a, b R_pos, c R:
    a != 1
    a^c = b
    =>:
        log(a, b) = c

# Useful evaluation-style examples that should stay easy.

log(2, 2^5) = 5
log(2, 32 / 4) = log(2, 32) - log(2, 4) = 5 - 2 = 3
log(2, 8 * 4) = log(2, 8) + log(2, 4) = 3 + 2 = 5
log(4, 64) = log(2^2, 64) = log(2, 64) / 2 = 6 / 2 = 3
log(3, 9^2) = 2 * log(3, 9) = 2 * 2 = 4

# Additional builtin logarithm rules.

forall a, x R_pos:
    a != 1
    =>:
        log(a, 1 / x) = -log(a, x)

forall a, b, c R_pos:
    a != 1
    b != 1
    c != 1
    log(c, a) != 0
    =>:
        log(a, b) = log(c, b) / log(c, a)

forall a, x, y R_pos:
    a > 1
    x < y
    =>:
        log(a, x) < log(a, y)

forall a, x, y R_pos:
    a < 1
    x < y
    =>:
        log(a, x) > log(a, y)

forall a, x R_pos:
    a > 1
    x > 1
    =>:
        log(a, x) > 0

forall a, x R_pos:
    a > 1
    x < 1
    =>:
        log(a, x) < 0

forall a, b R_pos, c R:
    a != 1
    =>:
        log(a, b) = c
    <=>:
        a^c = b
```

## 15. `modulo`

- Category: `builtin rule`
- System surface: `modulo`
- Purpose: Shows modular arithmetic and congruence-style reasoning.

```litex
# Mod: congruence under a common modulus (+, -, *) plus nested mod absorption (see builtin verify rules).

prove:
    have X Z
    have Y Z
    have m Z_nz
    (X + Y) % m = ((X % m) + (Y % m)) % m
    (X - Y) % m = ((X % m) - (Y % m)) % m
    (X * Y) % m = ((X % m) * (Y % m)) % m

prove:
    have b Z
    have c Z
    have d Z_nz
    (b * c) % d = ((b % d) * (c % d)) % d

prove:
    have a Z
    have b Z
    have c Z
    have d Z_nz
    (a + b * c) % d = ((a % d) + ((b % d) * (c % d)) % d) % d

forall m Z:
    m != 0
    =>:
        0 % m = 0

forall x Z:
    x % 2 = 0 or x % 2 = 1

forall x Z:
    x % 1 = 0

prove:
    prop mod_eq(a Z, b Z, n Z):
        exist k Z st {a - b = n * k}

    claim:
        prove:
            $mod_eq(11, 3, 4)
        witness exist k Z st {11 - 3 = 4 * k} from 2:
            11 - 3 = 4 * 2

    claim:
        prove:
            $mod_eq(-5, 1, 3)
        witness exist k Z st {(-5) - 1 = 3 * k} from -2:
            (-5) - 1 = 3 * (-2)

    claim:
        prove:
            forall a, b, c, d, n Z:
                $mod_eq(a, b, n)
                $mod_eq(c, d, n)
                =>:
                    $mod_eq(a + c, b + d, n)
        have by exist x Z st {a - b = n * x}: x
        have by exist y Z st {c - d = n * y}: y
        witness exist k Z st {(a + c) - (b + d) = n * k} from x + y:
            (a + c) - (b + d) = (a - b) + (c - d) = n * x + n * y = n * (x + y)

    claim:
        prove:
            forall a, b, c, d, n Z:
                $mod_eq(a, b, n)
                $mod_eq(c, d, n)
                =>:
                    $mod_eq(a - c, b - d, n)
        have by exist x Z st {a - b = n * x}: x
        have by exist y Z st {c - d = n * y}: y
        witness exist k Z st {(a - c) - (b - d) = n * k} from x - y:
            (a - c) - (b - d) = (a - b) - (c - d) = n * x - n * y = n * (x - y)

    claim:
        prove:
            forall a, b, n Z:
                $mod_eq(a, b, n)
                =>:
                    $mod_eq(-a, -b, n)
        have by exist x Z st {a - b = n * x}: x
        witness exist k Z st {(-a) - (-b) = n * k} from -x:
            (-a) - (-b) = -(a - b) = -(n * x) = n * (-x)

    claim:
        prove:
            forall a, b, c, d, n Z:
                $mod_eq(a, b, n)
                $mod_eq(c, d, n)
                =>:
                    $mod_eq(a * c, b * d, n)
        have by exist x Z st {a - b = n * x}: x
        have by exist y Z st {c - d = n * y}: y
        witness exist k Z st {a * c - b * d = n * k} from x * c + b * y:
            a * c - b * d = (a - b) * c + b * (c - d) = n * x * c + b * (n * y) = n * (x * c + b * y)

    claim:
        prove:
            forall a, b, n Z:
                $mod_eq(a, b, n)
                =>:
                    $mod_eq(a^2, b^2, n)
        have by exist x Z st {a - b = n * x}: x
        witness exist k Z st {a^2 - b^2 = n * k} from x * (a + b):
            a^2 - b^2 = (a - b) * (a + b) = n * x * (a + b) = n * (x * (a + b))

    claim:
        prove:
            forall a, b, n Z:
                $mod_eq(a, b, n)
                =>:
                    $mod_eq(a^3, b^3, n)
        have by exist x Z st {a - b = n * x}: x
        witness exist k Z st {a^3 - b^3 = n * k} from x * (a^2 + a * b + b^2):
            a^3 - b^3 = (a - b) * (a^2 + a * b + b^2) = n * x * (a^2 + a * b + b^2) = n * (x * (a^2 + a * b + b^2))

    claim:
        prove:
            forall a, n Z:
                $mod_eq(a, a, n)
        witness exist k Z st {a - a = n * k} from 0:
            a - a = n * 0

    claim:
        prove:
            forall a, b Z:
                $mod_eq(a, 2, 4)
                =>:
                    $mod_eq(a * b^2 + a^2 * b + 3 * a, 2 * b^2 + 2^2 * b + 3 * 2, 4)
        have by exist x Z st {a - 2 = 4 * x}: x
        witness exist k Z st {a * b^2 + a^2 * b + 3 * a - (2 * b^2 + 2^2 * b + 3 * 2) = 4 * k} from x * (b^2 + a * b + 2 * b + 3):
            a * b^2 + a^2 * b + 3 * a - (2 * b^2 + 2^2 * b + 3 * 2) = (a - 2) * (b^2 + a * b + 2 * b + 3) = 4 * x * (b^2 + a * b + 2 * b + 3) = 4 * (x * (b^2 + a * b + 2 * b + 3))

    claim:
        prove:
            forall a, b Z:
                $mod_eq(a, 2, 4)
                =>:
                    $mod_eq(a * b^2 + a^2 * b + 3 * a, 2 * b^2 + 2^2 * b + 3 * 2, 4)
        $mod_eq(b^2, b^2, 4)
        $mod_eq(a * b^2, 2 * b^2, 4)
        $mod_eq(a^2, 2^2, 4)
        $mod_eq(b, b, 4)
        $mod_eq(a^2 * b, 2^2 * b, 4)
        $mod_eq(a * b^2 + a^2 * b, 2 * b^2 + 2^2 * b, 4)
        $mod_eq(3, 3, 4)
        $mod_eq(3 * a, 3 * 2, 4)
        $mod_eq(a * b^2 + a^2 * b + 3 * a, 2 * b^2 + 2^2 * b + 3 * 2, 4)
```

## 16. `power`

- Category: `builtin rule`
- System surface: `power`
- Purpose: Shows exponent typing, identities, and inequalities.

```litex
0^0 = 1

forall a R:
    a^0 = 1

forall a R, m, n N:
    a^(m+n) = a^m * a^n

forall a Z, m, n Z:
    m >= 1
    n >= 1
    =>:
        a^(m+n) = a^m * a^n

forall a Z:
    a^1 = a

forall a, b R, n N:
    (a * b)^n = a^n * b^n

forall a Z, n N:
    a^n $in Z

forall a N, n N:
    a^n $in N

forall a N_pos, n N:
    a^n $in N_pos

forall a R_pos, m R:
    a * a^m = a^(m + 1)
    a^m * a = a^(m + 1)

forall a R_nz, m Z:
    a * a^m = a^(m + 1)
    a^m * a = a^(m + 1)

forall x, y R, m N_pos:
    x >= 0
    y >= 0
    x <= y
    =>:
        x^m <= y^m

forall x, y R, m N_pos:
    x >= 0
    y >= 0
    x^m <= y^m
    =>:
        x <= y

forall x, y R_pos, q R:
    q > 0
    x > y
    =>:
        x^q > y^q

forall x, y R_pos, q Q:
    q > 0
    x > y
    =>:
        x^q > y^q

forall x R_pos, q R:
    x^q > 0
    x^q != 0
    x^q * x^(-q) = x^(q + (-q))
    q + (-q) = 0
    x^(q + (-q)) = x^0
    x^0 = 1
    x^q * x^(-q) = 1
    x^(-q) = 1 / x^q

know:
    forall x, y R, m N_pos:
        x >= 0
        y >= 0
        =>:
            x^m <= y^m
        <=>:
            x <= y
```

## 17. `speical_properties`

- Category: `builtin rule`
- System surface: `special numeric properties`
- Purpose: Shows special builtin numeric facts.

```litex
# Order chains using <=, =, < (or >=, =, >) get transitive closure when stored.
let a, b, c R, d R:
    a < b = c <= d

a < d
```

## 18. `standard_set`

- Category: `obj`
- System surface: `standard numeric sets`
- Purpose: Shows membership and subset facts for N, Z, Q, and R.

```litex
have a, b R, c Z

a $in R
b $in R
c $in Z

1 $in N
1 $in N_pos
1 $in Z
1 $in Q
1 $in R

1 $in Q_pos
1 $in R_pos
-1 $in R_neg
-1.1 $in Q_neg
-1 $in Z_neg
1 $in Q_nz

1 + 1 $in N

-1 + 32.123 $in Q

2 - 9.5 + 10.5 $in Z

1 - 5 $in Z_neg
2 + 3 $in N_pos
4 - 1 $in N

-0.5 * 6 $in Q_neg
1 - 2.25 $in Q_neg
0 - 3 $in R_neg

-2 * 2.5 $in R_neg
7 - 3 $in Q_nz
10 - 10 + 1 $in Q_nz

3 - 1 $in Q_pos
1 + 0.5 $in Q_pos

forall a, b N:
    a + b $in N
    a * b $in N

forall a N_pos, b N:
    a + b $in N_pos
    b + a $in N_pos

forall a, b N_pos:
    a * b $in N_pos

forall a Q:
    a > 0
    =>:
        a $in Q_pos
        a / 2 $in Q_pos

forall a R:
    a > 0
    =>:
        a $in R_pos
```

## 19. `sum_and_product`

- Category: `builtin rule`
- System surface: `sum and product`
- Purpose: Shows finite sums/products and induction with product facts.

```litex
sum(1, 3, 'Z(x){x}) = sum(1, 3, 'Z(x){x})
product(1, 3, 'Z(x){x}) = product(1, 3, 'Z(x){x})
sum(1, 3, 'Z(x){x}) = sum(1, 3, 'Z(y){y})
product(1, 3, 'Z(x){x}) = product(1, 3, 'Z(y){y})

eval sum(1, 3, 'Z(x){x})
eval product(1, 3, 'Z(x){x^2})
eval sum(1, 2, '(x Z) Z {sum(2, 3, '(y Z) Z {x + y})})
eval sum(0, 0, '(x Z) Z {sum(0, x, '(y Z) Z {x + y})})


# Point-wise: sum f = sum g + sum h on the same range.
sum(1, 3, '(x Z) Z {x + x}) = sum(1, 3, '(x Z) Z {x}) + sum(1, 3, '(x Z) Z {x})

# Merge adjacent index ranges: sum(a..b) + sum((b+1)..c) = sum(a..c), same summand.
sum(1, 3, '(x Z) Z {x + x}) + sum(4, 6, '(x Z) Z {x + x}) = sum(1, 6, '(x Z) Z {x + x})

# Constant summand: length * c when c does not use the index.
prove:
    have c Z
    sum(1, 3, '(x Z) Z {c}) = ((3 - 1) + 1) * c

# Finite-set sum: sum the function value over each element of a finite set.
sum_of_finite_set({1, 2, 3}, 'Z(x){x}) = 1 + 2 + 3
sum_of_finite_set({}, 'Z(x){x}) = 0
sum_of_finite_set(1...3, 'Z(x){x}) = sum(1, 3, 'Z(x){x})
sum_of_finite_set({1, 2}, 'Z(x){x}) $in Z
sum_of_finite_set({1, 2}, 'N_pos(x){x}) $in N_pos

prove:
    have X finite_set
    have c Z
    sum_of_finite_set(X, '(x X) Z {c}) = count(X) * c

prove:
    have X power_set(Z)
    know $is_finite_set(X)
    sum_of_finite_set(X, '(x X) Z {x + 0}) = sum_of_finite_set(X, '(x X) Z {x})

# Finite-set product: multiply the function value over each element of a finite set.
product_of_finite_set({2, 3, 4}, 'Z(x){x}) = 2 * 3 * 4
product_of_finite_set({}, 'Z(x){x}) = 1
product_of_finite_set(1...3, 'Z(x){x}) = product(1, 3, 'Z(x){x})
product_of_finite_set({1, 2}, 'Z(x){x}) $in Z
product_of_finite_set({1, 2}, 'N_pos(x){x}) $in N_pos
product_of_finite_set({}, 'N_pos(x){x}) $in N_pos

prove:
    have X finite_set
    have c R
    product_of_finite_set(X, '(x X) R {c}) = c ^ count(X)

prove:
    have X power_set(Z)
    know $is_finite_set(X)
    product_of_finite_set(X, '(x X) Z {x + 0}) = product_of_finite_set(X, '(x X) Z {x})

# Reindex: same summand, parallel shift of both bounds, pointwise on the (rhs) range.
sum(1, 3, '(x Z) Z {x}) = sum(2, 4, '(x Z) Z {x - 1})

# Last index: sum(s..e,f) = sum(s..e-1,f) + f(e) (same unary f); product analogue with *.
sum(1, 3, '(x Z) Z {x}) = sum(1, 2, '(x Z) Z {x}) + '(x Z) Z {x}(3)
product(1, 3, '(x Z) Z {x}) = product(1, 2, '(x Z) Z {x}) * '(x Z) Z {x}(3)

# Partition: sum(a..d,f) as edge-to-edge sub-sums (same f); product analogue with *.
sum(1, 10, '(x Z) Z {x}) = sum(1, 3, '(x Z) Z {x}) + sum(4, 8, '(x Z) Z {x}) + sum(9, 10, '(x Z) Z {x})

prove:
    sum(1, 3, 'Z(x){x}) = sum(1, 2, 'Z(x){x}) + 'Z(x){x}(3)
    product(1, 3, 'Z(x){x}) = product(1, 2, 'Z(x){x}) * 'Z(x){x}(3)

    sum(1, 10, 'Z(x){x}) = sum(1, 3, 'Z(x){x}) + sum(4, 8, 'Z(x){x}) + sum(9, 10, 'Z(x){x})

eval sum(1, 3, 'Z(x){sum(1, x, 'Z(y){x + y})})

prove:
    by induc a from 1:
        prove:
            product(1, a, 'N_pos(x){x}) % a = 0 and a <= product(1, a, 'N_pos(x){x})

        product(1, 1, 'N_pos(x){x}) = 1
        1 <= product(1, 1, 'N_pos(x){x})

        claim:
            prove:
                forall k Z:
                    k >= 1
                    product(1, k, 'N_pos(x){x}) % k = 0 and k <= product(1, k, 'N_pos(x){x})
                    =>:
                        product(1, k + 1, 'N_pos(x){x}) % (k + 1) = 0 and k + 1 <= product(1, k + 1, 'N_pos(x){x})

            product(1, k + 1, 'N_pos(x){x}) = product(1, k, 'N_pos(x){x}) * (k + 1)
            witness exist t Z st {product(1, k + 1, 'N_pos(x){x}) = t * (k + 1)} from product(1, k, 'N_pos(x){x})
            product(1, k + 1, 'N_pos(x){x}) % (k + 1) = 0
            k + 1 <= product(1, k + 1, 'N_pos(x){x})
```
