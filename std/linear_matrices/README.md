# Supplied-field matrix spaces

This module reuses native `matrix(K,m,n)`: two-argument functions on the
complete row and column ranges. Dimensions are natural numbers, including zero.
It constructs pointwise operations and an actual
`Algebra::vector_space::VectorSpace<K,F,matrix(K,m,n)>` from a supplied
`Algebra::field::Field<K>`.

Import `Matrices = linear_matrices`. The `space` export provides:

- `field_zero_matrix<K,F,m,n>`;
- `field_matrix_add<K,F,m,n>(A,B)`;
- `field_matrix_smul<K,F,m,n>(a,A)`;
- `field_matrix_space<K,F,m,n>`.

The callable declarations use literal function signatures definitionally equal
to the same matrix carrier. Public carrier, signature, operation and entry
theorems make those relationships available to importing proofs. In particular,
release `matrix_carrier_is_nonempty(K,m,n)` before a generic goal whose
VectorSpace type requires a nonempty matrix carrier.

The `native_compatibility` export proves six whole-function equalities:
zero, addition and scaling for the existing real and complex Field instances
agree with native `zero_matrix`, `matrix_add` and `matrix_scale`.
The source operations have distinct fixed names and contracts. Native matrix
rank, determinant and inverse interfaces retain their existing scalar scope.

Validation currently covers 38 strict source statements, generic imported
interfaces, actual 2-by-3 real/complex calculations and the 0-by-3, 2-by-0 and
0-by-0 matrix spaces. Five controls reject a shape mismatch, an invalid index,
a nonreal scalar in the real field, a complex matrix in the real carrier and
an incorrect calculated value. Each refusal is followed by a valid retained
conclusion.

The final saved-file and clean imported boundary gates pass; see
`validation/.ladr/acceptance.json`. The accepted correspondence is
LADR 3.29, 3.34, 3.36 and 3.39. The selected A-B ledger is now 88/119. The vector-space
part of 3.40 is available, but its dimension formula remains unproved.

Representing matrices, reconstruction, matrix-space dimension, products,
row/column rank correspondence, linear systems and changes of basis remain
future source work. Full FTA is also unfinished. There are no new native rules,
trust declarations or mathematical assumptions.

Run the task-owned checker from the repository root with the pinned executable:

```sh
LITEX_STD_PATH="$PWD/std" \
LITEX_CHECK_BINARY="$PWD/std/algebra/validation/.ladr_ab/.session-litex" \
python3 std/linear_matrices/validation/.ladr/check.py
```

The checker reuses the polynomial validation helpers, records the executable
and recursively consumed source hashes, and skips a saved gate only when its
snapshot and planned cases match. See `validation/.ladr/source_session.json`,
`use/prefix_session.json` and `use/session.json` for proof iterations.
