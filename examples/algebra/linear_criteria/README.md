# Linear criteria and bijective inverses

main.lit reuses the supplied real-plane model. It proves that coordinate
exchange (x,y)->(y,x) is linear and injective, applies the equal-dimension
criterion to get bijectivity, obtains a linear inverse, and checks inverse(3,4)
=(4,3), rank2 and nullity0. It exercises both directions of the rank/nullity
criteria and the dimension bounds through their exported names.

contracts.lit forwards the needed constructor/value domains and consumes all
22 new named theorems plus the inverse function carrier. Its inverse and
range/surjectivity contracts quantify over arbitrary sets, including empty
sets. Its inverse-linearity contract has no finite-dimensional hypothesis.

boundaries/main.lit uses the existing zero-space fixture to check dimension0
and the inverse of its identity map, then checks the empty-set bijection.
inverse_sets/main.lit is the complete independent README consumer for that
empty bijection. No empty inverse argument is valid.

The twenty negative configurations each withhold a required proof/domain or
ask for a wrong concrete conclusion, and reject only the final statement.
They test the exact submitted use, not a general theorem of logical negation.

Run from the repository root:

```sh
python3 examples/algebra/linear_criteria/check.py --binary /path/to/litex
```

The checker also copies the actual binary and std into archive/shared-data
layouts and tests discovery without LITEX_STD_PATH, then compares the full
current std/WiX inventory. Unrelated packaged modules are not mathematically
certified by this algebra batch.

The source is strict and trust-free, with no native or Rust change. Selection
requires a proved bijection; inverse linearity additionally requires actual
linearity. Finite-dimensional criteria retain their exact selected-value
domains. No canonical basis/complement or isomorphism-existence construction
is introduced. Direct sums and representation matrices remain future work.
