# First Steps

Small examples for the first Litex loop: write a mathematical fact, check it,
and reuse it on the next line.

The purpose line says what the example is for. Start with the code, then use the
short note to see where the same move belongs in a larger proof.

## 1. `calculation`

- Category: `fact`
- Purpose: Shows direct arithmetic and equality-chain verification.

```litex
1=1
1+1=2
3*8+10 = 34
2 ^ 2 = 4
1 % 2 = 1



abs(-1) = 1

1/(1/3+2) = 3/7

(-8/33)/(-8) = 1/33

3/(6/5) = 5/2

```

## 2. `equal_by_resolve`

- Category: `fact`
- Purpose: Shows how known equalities are resolved through local facts.

<!-- 问题：这里我其实想要突出的是，如果一个符号等于了一个什么值，比如3， 1/3, (2+3)*4 这样的全部由数字构成的表达式，那么这个符号的值就被保存下来了，之后做=的证明的时候，这个东西出现在式子里，litex内核会做一次特殊处理：把等式里所有的存过值的符号都替换成值，然后做=的证明。 -->

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4

have a2 R = 1 / 4
(4 * a2 + 10) * 10 = 110
```

## 3. `equality`

- Category: `fact`
- Purpose: Shows equality reuse when the needed facts are local assumptions.

```litex
forall a, b R:
    a = b
    b + 2 = 3
    =>:
        a + 2 = b + 2
```

## 4. `example_in_readme`

- Category: `stmt`
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
- Purpose: Exercises rational-expression normalization and simplification.

```litex
forall a, b, c, d R:
    b != 0
    d != 0
    b * d != 0
    =>:
        (a + b)^ 2 = a * a + 1.5 * a * b + 2 * b ^2 - b ^ 2 + 0.5*b * a
        (a + b) * (c + d) = a * c + d * b + 2 * b * c + a*d*1 - c * b

        a / b + c / d = (a * d + c * b) / (b * d)
        a / (b * d) + c / (b * d) = (a + c) / (b * d)

        1 / 3 = 3 / 9
```

```litex
sketch:
    have a R = 1

    a + 2 = 3
```

```litex
sketch:
    have a R, b R = 1, 2
    (a + (a + (a * b + (a + b)))) * (a + 3 * b) = 49
```
