# Builtin Verification Rules

## Equalities

### Must-Know
Left and right are numeric expressions built from numbers and arithmetic operators (`+`, `-`, `*`, `/`, `^` with natural number exponents). The verifier can evaluate both sides and compare final values.

```litex
2 + 3 * 4 = 14
```

Modulo arithmetic on integers is evaluated directly by the builtin calculation rule.

```litex
4 % 2 = 0
```

For polynomial-style arithmetic expressions, Litex can normalize both sides and verify equality after simplification.

```litex
forall a, b R:
    (a + b)^2 = a^2 + a*b + b^2 + b*a
```

For fraction equalities, the verifier may use cross-multiplication (`a / b = c / d` ⇔ `a * d = b * c`) under valid denominator conditions.

```litex
2 / 3 = 4 / 6
```

If a symbol is already known to be equal to a numeric value, the verifier can substitute that value in later calculations.

```litex
have a R = 2
a ^ 2 = 4
```

If a function definition is known (`have fn ... = ...`), the verifier can instantiate the function body with concrete arguments when checking equalities of function applications.

```litex
have fn f(x R) R = x + 1
f(2) = 3
```