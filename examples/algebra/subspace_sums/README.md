# Finite subspace sums and Grassmann dimension

This project imports std/algebra as Algebra and reuses the real-plane model
from dimension_extension. Run:

```sh
python3 examples/algebra/subspace_sums/check.py --binary /path/to/litex
```

main.lit checks both overlapping and disjoint sums. The repeated horizontal
axis has dim(U)+dim(U)=dim(U+U)+dim(U∩U)=1+1. Horizontal and vertical axes
have 1+1=2+0; Grassmann determines the vertical dimension from the other
three values. Both zero summands and full/zero in either order are covered.
Selected dimensions retain the actual inherited-space finiteness and numeric
carrier evidence needed by each theorem. The mathematical source does not
require a finite ambient space.

contracts.lit calls all 21 named source theorems over arbitrary fields and
spaces. intersection/main.lit is the complete isolated README example: one
finite summand is enough for a finite intersection. Nineteen independent
controls omit a mathematical/value-domain premise or give a wrong dimension.
The checker requires every preceding statement to pass and only the final
statement to fail at its recorded stage. Rejection does not prove negation.

The checker also executes actual copied binary/std installations in archive
and shared-data layouts without LITEX_STD_PATH, and compares the std payload
and WiX files/components. This is a focused algebra gate, not a global
release or Lean certification. The source contains no trust or user axiom.
