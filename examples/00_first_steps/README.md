# First Steps

Small examples for the first feedback loop: arithmetic facts, equality chains, direct calculations, and simple equations.

Each Litex block below is checked independently by `cargo test run_examples -- --nocapture`.
The `Category` and `System surface` fields say what part of Litex the example is meant to exercise.

## 1. `calculation`

- Category: `fact`
- System surface: `calculation chains`
- Purpose: Shows direct arithmetic and equality-chain verification.

```litex
1=1
1+1=2
3*8+10 = 34
2 ^ 2 = 4
1 % 2 = 1

have a R = 1 / 4
(4 * a + 10) * 10 = 110

abs(-1) = 1

1/(1/3+2) = 3/7

(-8/33)/(-8) = 1/33

3/(6/5) = 5/2

forall a R:
    a = (1.5)/(33/(-8))
    =>:
        10 * a = -40 / 11

eval 1 + 1 / 3
eval (1 / 3 + 1 / 6) * 2
```

## 2. `equal_by_resolve`

- Category: `fact`
- System surface: `known equality resolution`
- Purpose: Shows how known equalities are resolved through local facts.

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4

(1, 2)[1] = 1
(1, 2)[2] = 2

have a set = (1, 2)
a[1] = 1
a[2] = 2
```

## 3. `equality`

- Category: `fact`
- System surface: `equality facts`
- Purpose: Shows simple equality reuse from known background facts.

```litex
have a, b R
know a = b
know b + 2 = 3
a + 2 = b + 2
```

## 4. `example_in_readme`

- Category: `stmt`
- System surface: `forall statement`
- Purpose: Minimal first example used by the top-level README.

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4
```

## 5. `linear_equation`

- Category: `fact`
- System surface: `linear equation simplification`
- Purpose: Solves small linear equalities by explicit algebraic steps.

```litex
forall x, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14
    =>:
        y = 2 * (2 * x + 3 * y) - (4 * x + 5 * y) = 6
        x = ((2 * x + 3 * y) - 3 * y) / 2 = -4

forall a, b, c R:
    a + b = c
    =>:
        a = c - b

forall a, b, c R:
    b + a = c
    =>:
        a = c - b

forall x cart(R, R):
    3 * x[1] + 2 * x[2] = 12
    x[1] = 4
    =>:
        2 * x[2] = 12 - 3 * x[1] = 12 - 3 * 4 = 0
        x[2] = (2 * x[2]) / 2 = 0 / 2 = 0
```

## 6. `rational_expression_simplification`

- Category: `builtin rule`
- System surface: `rational expression simplification`
- Purpose: Exercises rational-expression normalization and simplification.

```litex
sketch:
    have a, b, c, d R
    know:
        b != 0
        d != 0
        b * d != 0

    (a + b)^ 2 = a * a + 1.5 * a * b + 2 * b ^2 - b ^ 2 + 0.5*b * a
    (a + b) * (c + d) = a * c + d * b + 2 * b * c + a*d*1 - c * b

    a / b + c / d = (a * d + c * b) / (b * d)
    a / (b * d) + c / (b * d) = (a + c) / (b * d)

    1 / 3 = 3 / 9

sketch:
    have a R = 1

    a + 2 = 3

sketch:
    have a R, b R = 1, 2
    (a + (a + (a * b + (a + b)))) * (a + 3 * b) = 49
```
