# Internal direct sums

This project imports std/algebra as Algebra and reuses the existing real-plane
model from dimension_extension. Run:

```sh
python3 examples/algebra/direct_sum/check.py --binary /path/to/litex
```

main.lit checks axis and oblique complementary projections, their exact values,
linearity, idempotence, images, kernels and the dimension formula. In particular,
the diagonal/vertical split sends(3,4) to(3,3) and(0,1). Both horizontal
summands fail the internal-direct-sum definition, proved by contradiction.

contracts.lit calls all 25 named source theorems over arbitrary fields and
spaces. The boundary project covers both full/zero orders and the inherited
zero space, including zero dimension and identity-idempotent splitting. The
idempotent project is the complete standalone std-only README example.

Twenty independent controls require their prefix to pass and only the final
statement to be rejected at its recorded mathematical/domain stage. Actual
archive/shared-data installations execute copied binary/std without
LITEX_STD_PATH. The checker also compares all packaged files and WiX component
references. These are focused algebra checks, not a global release or Lean
certification. There is no source trust or user axiom.

The construction is an internal direct sum of supplied subspaces. No inner
product, finite basis or canonical complement is assumed. Finite dimension is
used only by the dimension results, whose selected-value domains are explicit.
External direct sums and representation matrices remain separate work.
