# Dataset Formalization Guide

AI can translate problem statements into Litex code at scale, but the result
must still be checked against the original mathematical content. A generated
Litex proof is useful only if it represents the same assumptions and the same
conclusion as the source problem.

Use this simple problem as a running example:

> Positive real number `x` satisfies `x^3 = 8`, so `x + 3 = 5`.

A faithful Litex formalization should introduce the variable, record the
condition, and prove the requested conclusion:

```litex
forall x R_pos:
    x^3 = 8
    =>:
        x = (x^3)^(1/3) = 8^(1/3) = 2
        x + 3 = 2 + 3 = 5
```

## Common Pitfalls

1. AI generates working Litex code, but the code is unrelated to the problem statement.

For the running example, an AI might generate:

<!-- litex:skip-test -->

```litex
2 = 2
```

This code verifies, but it does not mention the variable `x`, the condition
`x^3 = 8`, or the desired conclusion `x + 3 = 5`.

2. AI might confuse with conditions and conclusions.

For the running example, an AI might generate:

<!-- litex:skip-test -->

```litex
2^3 = 8
2 + 1 = 3
```

Although this code verifies, it only proves isolated numeric facts. It does
not translate the assumption that an arbitrary positive real number `x`
satisfies `x^3 = 8`, and it does not prove `x + 3 = 5`.

3. AI might overuse `trust`.

For the running example, an AI might generate:

<!-- litex:skip-test -->

```litex
trust:
    x^3 = 8
    x + 3 = 5
```

This hides the core proof obligation instead of translating it. `trust` should
only be used for an explicitly labeled background fact or temporary proof debt,
not to replace the condition and conclusion of the problem itself.
