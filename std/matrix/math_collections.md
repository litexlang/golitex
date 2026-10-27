# Mathematical interfaces in `std/matrix`

The source is [main.lit](main.lit); import and examples are in [README.md](README.md).
Native operators are reused dependencies. This module introduces ordinary
functions and propositions, with checked source proofs of its named theorems.

## Carriers and constructions

The underlying carrier is an exact finite function: one index for a vector,
two simultaneous indices for a matrix. Standard R/C operations use explicit
natural dimensions. A matrix is distinct from a curried function of rows.

The thirteen templates provide a zero vector; vector addition, subtraction
and scalar multiplication; row, column, diagonal and selected-index functions;
kernel and image sets; characteristic polynomial and spectrum; and the guarded
inverse-based square-system solver. Set-valued functions remain constructions.
Source function dimensions use template parameters so that function signatures
retain their existing independent parameter/return-carrier scopes.

## Independent relations

`is_matrix_inverse(n,A,B)` means AB=I and BA=I with complete square domains.
`is_invertible_matrix` existentially quantifies the candidate. A selected inverse
can be used after det(A,n)≠0 is established; the source theorems connect the
candidate, existence and selected-value interfaces.

`has_matrix_rank_factorization(m,n,r,A,U,V,L,Right)` states A=UV, LU=I_r,
VRight=I_r and r≤m,n, together with all five domains. Thus U has independent
columns and V has independent rows. `has_matrix_rank` existentially quantifies
these factors; its definition is independent of equality to the rank operator.

The symmetry, Hermitian, orthogonal, unitary, normal, diagonal, triangular,
idempotent, projection, nilpotent and positivity predicates assert laws about
supplied matrices. A projection is self-adjoint and idempotent here. Positivity
uses the standard complex inner product and includes self-adjointness. The
linear-system and eigenpair predicates are relations; a nonzero eigenvector
and a diagonalization witness are supplied or existentially quantified.
No eigenvector or arbitrary solution selector is introduced.

## Proved theorem interfaces

| Source theorem | Mathematical result |
| --- | --- |
| `matrix_add_commutative` | Entrywise addition commutes |
| `matrix_add_associative` | Entrywise addition associates |
| `matrix_add_zero` | Zero is both a left and right additive identity |
| `matrix_sub_self` | Subtracting a matrix from itself gives the zero matrix |
| `matrix_scale_one` | Scaling by one preserves the matrix |
| `matrix_scale_zero` | Scaling by zero gives the zero matrix |
| `matrix_scale_distributive` | Scalar multiplication distributes over entrywise addition |
| `matrix_inverse_candidate_unique` | Two double-sided inverse candidates agree |
| `matrix_inverse_candidate_nonsingular` | A candidate proves det≠0 |
| `matrix_inverse_candidate_selected` | A candidate equals the selected inverse |
| `matrix_inverse_exists_from_determinant` | det≠0 gives an inverse candidate |
| `matrix_invertible_nonsingular` | Existence implies det≠0 |
| `matrix_rank_from_certificate` | Explicit rank factorization gives the exact rank |
| `matrix_rank_candidate_selected` | A rank candidate gives the selected rank value |
| `matrix_rank_candidate_unique` | Rank candidates agree |
| `matrix_rank_has_candidate` | The finite rank has a factorization candidate |
| `unitary_matrix_nonsingular` | A unitary matrix has nonzero determinant |
| `unitary_matrix_inverse` | Its inverse is its conjugate transpose |
| `solve_matrix_correct` | A⁻¹b solves the nondegenerate square system |
| `invertible_matrix_solution_unique` | Two solutions to that system agree |
| `solve_matrix_definition` | The guarded source solver equals the native inverse action |

## Dependency order

1. Standard scalars, exact finite function domains and finite sums.
2. Native matrix constructors, arithmetic, determinant, inverse and rank;
   native finite inner product and norms.
3. Ordinary vector helpers, inverse and rank relations, matrix properties.
4. Source inverse/rank theorems, then unitary inversion and system solving.
5. Kernel/image, spectrum and diagonalization interfaces for later developments.

The seven entrywise source laws depend only on native component formulas,
scalar identities and complete-domain function extensionality. Their source
calls preserve the former builtin argument order, with matrix membership as
explicit premises following set-kind binders. They work at all natural sizes,
including empty row or column domains. Their former native BT identities and
handlers have been removed; the other matrix schemas remain dependencies.

The module relies on native mathematical schemas for determinant, inverse and
rank theorems. It supplies no user axioms or unchecked proofs. Spectral
algorithms, general-field structures and numerical solvers are outside its
current claims. The native matrix Lean translation remains unsupported.
