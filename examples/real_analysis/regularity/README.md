# Finite regularity and smoothness

main.lit checks x^3 in C^3 on R from a supplied continuous derivative chain,
then lowers it to C^0. It also checks abs in C^0, ordinary relative continuity
and zero-order evaluation on an isolated domain, and constant smoothness for
unary and vector-input functions. Numerical derivative selection still follows
an explicit candidate proof.

scalar.lit checks x1*x2 in C^2 on cart_n(R,2). It supplies continuous candidate
functions for every length-1 and length-2 coordinate path, then applies the
source C^2 Schwarz theorem to paths(1,2) and(2,1) at(3,4), both with value1.
The function takes one vector argument.

```sh
LITEX_STD_PATH="$PWD/std" target/release/litex -strict -lang en -f examples/real_analysis/regularity/main.lit
LITEX_STD_PATH="$PWD/std" target/release/litex -strict -lang en -f examples/real_analysis/regularity/scalar.lit
```

The optional package is std/real_regularity. The boundary fixtures cover missing
regularity, wrong values, non-reversed paths, isolated domains, an invented
higher order, an incorrect constant formula and unary/vector/domain mismatch.
The focused installed test checks each rejection and subsequent Session
liveness. These examples do not claim general mixed-path permutation,
D^alpha, vector-output regularity or automatic differentiability.
