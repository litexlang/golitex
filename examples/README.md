# Litex Examples

This directory is a catalog of Litex language, proof, mathematics, and module
examples. Each public entry states the behavior it demonstrates and keeps the
corresponding Litex source close to that description.

## Public Reading Path

1. [`01_proof_patterns/`](01_proof_patterns/) contains small proof-control and
   theorem-reuse patterns, including explicit builtin finite-subset closure and
   one-based finite-set indexing.
2. [`02_builtin_math/`](02_builtin_math/) shows arithmetic, order, finite-set,
   function, and numeric rules provided by the verifier, including native
   natural-number primality and coprimality.
3. [`03_language_features/`](03_language_features/) covers definitions,
   settings, structs, well-definedness, imports, and the
   [empty finite-sequence literal](03_language_features/empty_finite_sequence.lit).
4. [`04_case_studies/`](04_case_studies/) contains larger worked proofs built
   from several interfaces.
5. [`08_module_repository/`](08_module_repository/) is a configured module
   project that demonstrates ordered exports and submodules.

The Litex-to-Lean source/generated pairs live with their target package in
[`lean/examples/`](../lean/examples/).

The numbering is a reading order, not a requirement that every number exist.
Public `.lit` files have descriptive names and are self-contained unless their
subject is specifically a configured module or import relationship.
