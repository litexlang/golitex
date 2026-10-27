# Regularity closure through imported source laws

The example imports the separately proved regularity examples as Base. It
proves C^3 of a shifted cubic, C^2 of a shifted x1*x2 function, and smoothness
of unary/vector-input linear combinations of constants. Every function keeps
its complete actual domain; the vector function takes one argument.

```sh
LITEX_STD_PATH="$PWD/std" target/release/litex -strict -lang en -f examples/real_analysis/regularity_laws/main.lit
```

The four optional source theorems consume both input regularity propositions
and a pointwise formula for the result. They introduce no automatic strategy or
new numerical selector. The ordinary relative example import avoids duplicating
the earlier cubic and coordinate-path proof chains.

The imported example definitions are opened with release obj def, and their
proved regularity is consumed through four explicitly released zero-parameter
source theorems. Bare facts from Base are not ambient assumptions. The saved
caller passed strict checking; six nearest refusal/liveness controls passed
the actual-import Session. No module visibility rule was changed.
