# Finite-dimensional linear-map rank and nullity

The std/algebra linear_dimension export proves rank-nullity over any supplied
field. Its source space is finite-dimensional; its target is arbitrary.

main.lit reuses the real plane from ../dimension_extension/model.lit and the
projection/axis facts from ../subspaces/main.lit. It computes:

| Map on R x R | Rank | Nullity |
| --- | ---: | ---: |
| (x,y) -> (x,0) | 1 | 1 |
| zero | 0 | 2 |
| identity | 2 | 0 |

The projection image has the one-vector axis basis. Rank-nullity gives its
kernel dimension. The empty image basis gives zero-map rank 0; the empty kernel
basis gives identity nullity 0, and rank-nullity gives the other dimensions.
The prior fixture receives only a named export of five already checked facts.

contracts.lit consumes all 21 new named theorems and the three source value
families. Rank requires only linearity and finite image; nullity requires only
linearity and finite kernel. Additional contracts check rank availability from
finite target alone and the definition equalities. empty_lists.lit checks empty
pieces and concatenation boundary entries. The negative directory contains
twenty independent configurations, each rejecting only its final statement.

Run from the repository root:

```sh
python3 examples/algebra/rank_nullity/check.py --binary target/release/litex
```

The checker also copies the actual executable and std into archive and
shared-data layouts and exercises std discovery without LITEX_STD_PATH. It
compares the complete current std payload with WiX; that inventory can include
unrelated std modules and does not certify their mathematics.

All maintained mathematics is strict and trust-free. No native rule, AST,
runtime, BT, overload or compiler change is needed. This batch does not cover
infinite/cardinal dimension, a canonical complement, representation matrices,
or the rest of the undergraduate curriculum.
