# Finite sums of unary real functions

The family is x^2, sin(x), abs(x), with an intentionally unused last derivative
entry99. Its first two terms have derivative1 at0; no derivative of abs at0 is
required for that prefix. The full three-term sum is proved continuous. Empty
prefixes and an empty numeric family are checked independently.

```sh
LITEX_STD_PATH="$PWD/std" target/release/litex -strict -lang en -f examples/real_analysis/function_sums/main.lit
```

The real-valued numeric prefix is computed through source zero, successor and
index-equality theorems. Every function keeps its actual domain. Six nearest
controls reject using the nondifferentiable tail, a false derivative/value,
an invalid prefix, an implicit domain restriction and an empty-sum derivative
on an isolated domain. Rejection is followed by a Session liveness check.
