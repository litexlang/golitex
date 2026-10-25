# Mathematical organization

The scalar field, vector space, subspace and linear-map interfaces come from
`std/algebra`. The examples supply instances and prove their required laws.
They do not redeclare the generic structures or forward a duplicate theorem family.

The real field uses the usual arithmetic operations and an inverse restricted
to nonzero inputs. The scalar line uses real addition and multiplication as
vector addition and scalar action. Doubling is additive and homogeneous, its
kernel is exactly `{0}`, and the imported zero-kernel theorem gives injectivity.
The converse theorem recovers the kernel equality. Identity, zero maps and
composition exercise function constructions; kernels/images use native
`preimage` and `fn_range` and become subspaces through shared theorems.

The singleton carrier has only the zero vector, with constant-zero addition
and scalar action. This case checks that vector-space nonemptiness does not
accidentally require a nonzero vector. Its scalar field still has distinct zero
and one. No basis/dimension selector or separate kernel/image construction is needed.

The rejection controls separate field nondegeneracy, inverse guards, vector-space
laws, subspace zero containment, full linearity, and the kernel equality required
for injectivity. In particular, a square map preserves zero without being linear;
a zero map is linear without being injective on the real line. The checker
verifies valid prefixes so a failed import cannot masquerade as a mathematical
rejection. Installed-layout checks exercise the actual shared source package.
