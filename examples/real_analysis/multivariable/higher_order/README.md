# Ordered finite partial derivatives

Import the ordinary `real_multivariable` source library as `Calc`. The example
checks zero order, the path `(1,1,2)` for `x(1)^2*x(2)^3`, an equivalent complete
function path, a proper domain `x(1)>0`, and both native second-order bridges.
Each function takes one vector input. The path means first coordinate 1,
then coordinate 1, then coordinate 2; its selected value at `(1,2)` is 24.

The source candidate is
`has_ordered_partial_at(n,D,k,f,p,indices,L)`. After proving it, explicitly
release `ordered_partial_candidate_exists` and `ordered_partial_value`.
The selector is `\Calc::higher_order::ordered_partial<n,D,k>(f,p,indices)`.
It has exactly three template parameters and three ordinary arguments.

`boundaries.json` supplies REPL setup and rejection controls. File declarations
have the `main::` namespace in the continued REPL. The installed standard-library
integration test loads the positive file once and checks rejection plus liveness
in the same process. A missing proof does not establish a negative mathematical
proposition. A tuple with one component uses `tuple(1)`; `(1)` is the scalar 1.

Run this file with a configured std location, for example from the repository:

```sh
LITEX_STD_PATH="$PWD/std" target/release/litex -strict -lang en -f examples/real_analysis/multivariable/higher_order/main.lit
```

No automatic path exchange, multi-index count interface or general high-order
linearity theorem is supplied by this example. The selectors use existing source
functions and unique-existence proofs, with no new native operator or BT.

The refusal controls also check that an outer multiplication by zero cannot hide an undefined higher derivative.


[successor.lit](successor.lit) uses the same polynomial at(2,2) along path1,1,2.
Its canonical first and second prefix functions retain the certificate's actual
intermediate domains, with values32 and16. Their next coordinate candidates are16
and24. This exercises arbitrary-order source coherence without sorting paths,
widening domains or introducing new native differentiation rules.

```sh
LITEX_STD_PATH="$PWD/std" target/release/litex -strict -lang en -f examples/real_analysis/multivariable/higher_order/successor.lit
```
