# Litex Builtin Rule Notes

This file is a working note for concrete builtin verification rules.

`docs/litex_builtin_semantics.md` should stay as the high-level conceptual map. Specific rule inventories can live here until they are organized into a more complete reference.

## Standard Number Set Closure

These rules verify membership in standard number sets from membership of direct operands.

```litex
forall a, b N:
    a + b $in N
    a * b $in N

forall a N_pos, b N:
    a + b $in N_pos
    b + a $in N_pos

forall a, b N_pos:
    a * b $in N_pos
```

Notes:

1. `N` is closed under addition and multiplication.
2. `N_pos + N` and `N + N_pos` are in `N_pos`.
3. `N_pos * N_pos` is in `N_pos`.
4. `N_pos * N` is not generally in `N_pos`, because the `N` operand may be `0`.

Related code:

```text
src/verify/verify_builtin_rules/in_fact_builtin.rs
```

## Absolute Value Rules

These rules describe basic absolute-value semantics currently handled by builtin verification.

```litex
forall x R:
    0 <= abs(x)
    x <= abs(x)
    -x <= abs(x)

forall x R:
    x ^ 2 = abs(x) ^ 2

forall x, y R:
    abs(x * y) = abs(x) * abs(y)
    abs(x + y) <= abs(x) + abs(y)
    abs(x - y) <= abs(x) + abs(y)
```

Related code:

```text
src/verify/verify_equality_by_builtin_rules.rs
src/verify/verify_builtin_rules/abs_order_builtin.rs
src/verify/verify_builtin_rules/number_compare.rs
```

## Power Rules

These rules describe exponent algebra that is handled directly by builtin verification.

```litex
forall a R, m, n N_pos:
    a^(m+n) = a^m * a^n
```

Notes:

1. The exponent rule is restricted to positive natural exponents, so `0^0` is not introduced.
2. The product side may also appear with the factors swapped.

Related code:

```text
src/verify/verify_equality_by_builtin_rules.rs
```
