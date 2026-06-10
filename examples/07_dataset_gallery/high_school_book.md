# High School Book

High-school textbook examples covering equality, inequalities, trigonometry, coordinate geometry, derivatives, and extrema records.

Each item gives the mathematical idea first, then the Litex code that checks it.

```litex
import Trig

have answer_0034 set = { p cart(R, R) : p[2] - 5 = 4 / 3 * (p[1] - 3) }
```

```litex
have fn average_change_rate(a R, h R_pos) R = (2 * pi * (a + h) - 2 * pi * a) / h
forall a R, h R_pos:
    average_change_rate(a, h) = 2 * pi
```

```litex
have fn average_change_rate(a R, h R_pos) R = (pi * (a + h)^2 - pi * a^2) / h
forall a R, h R_pos:
    average_change_rate(a, h) = pi * (2 * a + h)
```

```litex
forall a, b, c, d R:
    a = b
    c = d
    =>:
        a * c = b * d
```

```litex
forall a, b, c, d R:
    a = b
    c = d
    =>:
        a + c = b + d
```

```litex
forall a, b, c, d R:
    a = b
    c = d
    =>:
        a * c = b * d
```

```litex
forall a, b R:
    a = b
    a != 0
    =>:
        1 / a = 1 / b
```

```litex
forall a, b R, n N_pos:
    a = b
    =>:
        a ^ n = b ^ n
```

```litex
forall a, b R:
    a * b = 0
    =>:
        a = 0 or b = 0
```

```litex
forall a, b R:
    a * b = 0
    =>:
        a = 0 or b = 0
```

```litex
15 * pi / 180 = pi / 12
-108 * pi / 180 = -3 * pi / 5
22.5 * pi / 180 = pi / 8
have answer set = (pi / 12, -3 * pi / 5, pi / 8)
```

```litex
import Trig

Trig::sin(5 * pi / 3 + 2 * 0 * pi) = (-1 * sqrt(3)) / 2
Trig::cos(5 * pi / 3 + 2 * 0 * pi) = 1 / 2
Trig::cos(2 * pi / 3 + 1 * pi) != 0
Trig::tan(2 * pi / 3 + 1 * pi) = -1 * sqrt(3)
have answer set = ((-1 * sqrt(3)) / 2, 1 / 2, -1 * sqrt(3), (-1 * sqrt(3)) / 3)
```

```litex
import Trig
forall k Z:
    Trig::sin(k * pi) = 0

forall k Z:
    Trig::cos(2 * k * pi) = 1
    Trig::cos((2 * k + 1) * pi) = -1
```

```litex
import Trig

forall x R:
    0 <= x <= 1
    -1 <= x <= 1
    =>:
        Trig::sin(Trig::arcsin(x)) = x
        Trig::cos(Trig::arccos(x)) = x

forall y R:
    0 <= y <= pi / 2
    -pi / 2 <= y <= pi / 2
    0 <= y <= pi
    =>:
        Trig::arcsin(Trig::sin(y)) = y
        Trig::arccos(Trig::cos(y)) = y

forall x R:
    -1 <= x <= 1
    =>:
        Trig::sin(Trig::arcsin(x)) = x
        Trig::cos(Trig::arccos(x)) = x

forall y R:
    -pi / 2 <= y <= pi / 2
    =>:
        Trig::arcsin(Trig::sin(y)) = y

forall y R:
    0 <= y <= pi
    =>:
        Trig::arccos(Trig::cos(y)) = y
```

```litex
import Trig

forall x R:
    0 < 1 + x^2
    =>:
        Trig::cos(Trig::arctan(x)) > 0
        Trig::tan(Trig::arctan(x)) = x

forall y R:
    -pi / 2 < y < pi / 2
    =>:
        Trig::arctan(Trig::tan(y)) = y
```

```litex
import Trig
have answer_0059_1 set = (pi / 6, pi / 3, 7 * pi / 6, 4 * pi / 3)
have answer_0059_2 set = {x R: (x - pi / 12) / pi / 2 $in Z or (x + 5 * pi / 12) / pi / 2 $in Z}
have answer_0059_3 set = {x R: (x - pi / 4) / pi * 2 $in Z}
```

```litex
import Trig

forall x R:
    0 <= x <= 1
    -1 <= x <= 1
    =>:
        Trig::sin(Trig::arcsin(x)) = x
        Trig::cos(Trig::arccos(x)) = x

forall y R:
    0 <= y <= pi / 2
    -pi / 2 <= y <= pi / 2
    0 <= y <= pi
    =>:
        Trig::arcsin(Trig::sin(y)) = y
        Trig::arccos(Trig::cos(y)) = y

forall x R:
    -1 <= x <= 1
    =>:
        Trig::sin(Trig::arcsin(x)) = x
        Trig::cos(Trig::arccos(x)) = x

forall y R:
    -pi / 2 <= y <= pi / 2
    =>:
        Trig::arcsin(Trig::sin(y)) = y

forall y R:
    0 <= y <= pi
    =>:
        Trig::arccos(Trig::cos(y)) = y
```

```litex
import Trig

forall x R:
    0 < 1 + x^2
    =>:
        Trig::cos(Trig::arctan(x)) > 0
        Trig::tan(Trig::arctan(x)) = x

forall y R:
    -pi / 2 < y < pi / 2
    =>:
        Trig::arctan(Trig::tan(y)) = y
```

```litex
have fn arithmetic_mean(x, y R) R = (x + y) / 2
have fn geometric_mean(x, y R: x >= 0, y >= 0) R = sqrt(x * y)

claim:
    prove:
        forall x, y R:
            x >= 0
            y >= 0
            =>:
                geometric_mean(x, y) <= arithmetic_mean(x, y)
    x * y >= 0
    sqrt(x * y)^2 = x * y
    (x + y)^2 - 4 * x * y = (x - y)^2
    0 <= (x - y)^2
    0 <= (x + y)^2 - 4 * x * y
    4 * x * y <= (x + y)^2
    x * y <= (x + y)^2 / 4
    ((x + y) / 2)^2 = (x + y)^2 / 4
    x * y <= ((x + y) / 2)^2
    0 <= sqrt(x * y)
    0 <= (x + y) / 2
    by contra sqrt(x * y) <= (x + y) / 2:
        sqrt(x * y) > (x + y) / 2
        sqrt(x * y)^2 > ((x + y) / 2)^2
        impossible x * y <= ((x + y) / 2)^2
    geometric_mean(x, y) = sqrt(x * y)
    arithmetic_mean(x, y) = (x + y) / 2
    geometric_mean(x, y) <= arithmetic_mean(x, y)
```
