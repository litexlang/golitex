# Fields, vector spaces and linear maps from std

These consumers import the actual `algebra` std package. Run from the repository
root after building the release executable:

```bash
python3 examples/algebra/vector_spaces/check.py
```

The checker sets `LITEX_STD_PATH` for checkout runs, checks all statement verdicts
and failure locations, then copies the actual std payload into two installed
layouts and runs the consumer without a path override. It also compares the
complete source package inventory with the WiX fragment. The full linear-algebra
lecture is included; local textbook projects are not part of this gate.

[main.lit](main.lit) constructs the real field and its one-dimensional scalar
vector space. It verifies the complete doubling map, computes its kernel, and
uses every one of the twelve shared theorem interfaces. Its final criterion is:

```litex
by thm Algebra::vector_space::zero_kernel_is_injective(R,real_field,R,scalars,R,scalars,double) => $injective(R,R,double)
```

This excerpt uses the preceding field, space, linearity and kernel facts in
`main.lit`; it is not a standalone file. Before promotion, the criterion and its
VectorSpace/linearity interfaces were owned by the lecture. The consumer now
uses explicit `Algebra::field` and `Algebra::vector_space` paths without a local
copy of the generic definitions or proofs.

[zero_dimensional/main.lit](zero_dimensional/main.lit) independently constructs
the singleton vector space over the real field. Identity and zero maps, their
kernels, ranges and the injectivity criterion remain valid in this allowed case.

The [shared fixture context](negative/context.lit) constructs valid instances
and complete functions. Each negative file opens those imported definitions,
accepts every valid prefix statement, and rejects only its final statement:

| Fixture | Required rejection |
| --- | --- |
| `inverse_at_zero` | Inverse application fails the nonzero well-definedness guard |
| `collapsed_field` | Zero equals one, so field membership fails |
| `affine_not_linear` | Translation cannot supply the linearity premise of zero preservation |
| `square_not_linear` | Preserving zero alone does not establish additivity and homogeneity |
| `missing_zero_kernel` | The zero map is linear but cannot supply singleton-kernel equality on R |
| `empty_subspace` | The empty subset does not contain vector zero |
| `wrong_scalar_action` | The constant-zero action on R fails the unit action law |

There is no source `trust`, `axiom` or `abstract_prop`, no extra native rule and
no finite-dimensional assumption in the kernel criterion. The source package
and complete interfaces are documented in [std/algebra](../../../std/algebra/README.md).
The [real-plane lecture](../../../showcases/linear_algebra/README.md) consumes the
same foundations. These examples do not establish general basis existence,
basis-length invariance or a dimension selector.

[math_collections.md](math_collections.md) records the mathematical decomposition.
