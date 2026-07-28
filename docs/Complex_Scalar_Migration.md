# Complex Scalar Migration

Litex 0.9.110-beta introduces a native symbolic complex scalar system. This is
a preview semantic migration: `C`, `i`, `re`, `img`, and `C_abs` are now
hard-reserved builtin names.

## What Changed

`C` extends the standard number-set chain:

```text
N ⊆ Z ⊆ Q ⊆ R ⊆ C
```

The operators `+`, `-`, `*`, unary `-`, and nonzero division accept complex
operands. Existing narrow inference remains preferred, so an integer or real
operation does not become merely complex. Natural powers are defined on `C`;
the additional integer-exponent branch requires a nonzero base.

The initial native interface is:

- `i $in C` and `i * i = -1`;
- `re, img : C -> R`;
- `C_abs : C -> R`;
- coordinate reconstruction and extensionality;
- complex-valued interval and finite-set sums and products.

Order and real analysis have not changed domains. Comparisons, signs, real
intervals, `abs`, `sqrt`, and `log` still require real operands. The preview
does not define general complex exponentiation, conjugation, branch cuts,
complex matrices, or the later modulus laws.

## Reserved-Name Migration

There is no legacy parser or soft-shadowing mode. Every declaration, binder,
index, and field named exactly `C`, `i`, `re`, `img`, or `C_abs` must be
renamed. Longer identifiers such as `ComplexPair`, `index`, `real_part`, and
`imaginary_part` are unaffected.

Use a mechanical name only when it remains clear in context:

| Previous ordinary identifier | Suggested replacement |
|---|---|
| set or local object `C` | `c`, or a semantic set name |
| index `i` | `i1`, `k`, `idx`, `row_idx`, or `col_idx` |
| ordinary function or field `re` | `real` or `real_part` |
| ordinary function or field `img` | `imag` or `imag_part` |
| ordinary identifier `C_abs` | a source-specific semantic name |
| user-defined `struct C` | `struct ComplexPair` |

For example, old source may have used:

```text
have C finite_set
forall i C:
    ...
```

The direct migration is:

```litex
have c finite_set
forall i1 c:
    i1 $in c
```

For a user-defined complex record, keep the original construction distinct
from the native scalar system:

```text
struct C:
    re R
    im R
```

A compatible rename is:

```litex
struct ComplexPair:
    real_part R
    imag_part R
```

This rename does not assert that `&ComplexPair` is `C`, and it does not identify
an older `complex_abs`, `complex_absolute_value`, or `norm` definition with
the native `C_abs`.

## New Native Examples

Each block below is self-contained.

```litex
i $in C
i^2 = -1
i^4 = 1
i^(-1) = -i
```

```litex
forall a, b R:
    re(a + b * i) = a
    img(a + b * i) = b

forall z C:
    z = re(z) + img(z) * i
    C_abs(z) = sqrt(re(z)^2 + img(z)^2)
```

```litex
sum(1, 3, fn(k Z) C {k + i}) $in C
product(1, 3, fn(k Z) C {k + i}) $in C
finite_set_sum({1, 2}, fn(k Z) C {k + i}) $in C
finite_set_product({1, 2}, fn(k Z) C {k + i}) $in C
```

## Backend Boundary

Complex reasoning and aggregation are symbolic in this release. The evaluator
does not add a complex runtime value, and the current Python and Lean
extractors do not lower genuinely complex-valued expressions. They report the
unsupported form instead of silently generating `float` or `ℝ` code.

Existing textbook-defined complex structures remain valid mathematical models
after their reserved identifiers are renamed. They are not automatically
migrated to the native `C` interface.
