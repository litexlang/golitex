# Finite function sums with one vector input

The two functions are x1^2 and x2^3 on cart_n(R,2). At(1,2), their axis-1
partial candidates are2 and0; the source sum theorem proves the sum's partial2.
The sum is also continuous at this Euclidean interior point.

```sh
LITEX_STD_PATH="$PWD/std" target/release/litex -strict -lang en -f examples/real_analysis/multivariable/function_sums/main.lit
```

The function takes one vector argument and returns a real number. Six nearest
controls cover false values, out-of-range axes/prefixes, a unary function family
in place of a vector-input family, and a missing premise of the explicit
interior-continuity theorem. The latter is a sufficient theorem's boundary;
it does not assert noncontinuity on isolated domains.
