# Rational-expression calculation

Litex checks equalities such as `2 * i + 1 = i * i + 2 + 2 * i` in [`54_ComplexAlgebraicCalculation.lit`](../../lean/examples/54_ComplexAlgebraicCalculation.lit); a lone `x ^ 2 - 1` does not request factorization.

```litex
2 * i + 1 = i * i + 2 + 2 * i
forall a, b R:
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2

forall x R:
    x != 0
    =>:
        (x - x / 2) / x = 1 / 2
```

```text
compare left and right
  -> evaluate closed numeric pieces such as 1.5 / 3
  -> expand supported literal powers such as (a + b) ^ 2
  -> collect and sort commutative monomials
  -> in complex mode, replace each pair i * i with -1
  -> accept only when both collected forms are equal
```

## Examples and limits

| Form | Accepted example | Nearest limit example |
| --- | --- | --- |
| Exact numbers | `1.5 / 3 = 1 / 2` | `1 / 0` is rejected, not approximated. |
| Polynomial algebra | `(a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2` | `(a + b) ^ n` is not expanded for symbolic `n`. |
| Rational expressions | From `x != 0`, Litex verifies `(x - x / 2) / x = 1 / 2`. | Without `x != 0`, the same expression reports `divisor x must be non-zero`. |
| Algebra around function values | `(sin(x) + 1) ^ 2 = sin(x) ^ 2 + 2 * sin(x) + 1` treats `sin(x)` as one algebraic atom. | `sin(x) ^ 2 + cos(x) ^ 2 = 1` needs the trigonometry rule, not rational normalization. |
| Builtin complex `i` | `i * i = -1` and `1 / i = -1 * i`. | For an ordinary `j C`, Litex does not infer `j * j = -1`. |

## Use it this way

Submit the target equality, for example `x ^ 2 - 1 = (x - 1) * (x + 1)`, and put required premises beside it, for example `x != 0 =>: x ^ 2 / x = x`.

```bash
cargo test --release rational_expression::algebraic_normalization::algebraic_identity_tests
target/release/litex -compact -strict -isolated -runner -f lean/examples/54_ComplexAlgebraicCalculation.lit
```
