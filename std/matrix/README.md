# Finite matrix algebra

This module supplies ordinary source definitions and proved theorems on top of
native real and complex matrix operations. Matrices remain exact finite
functions. Invertibility, positive definiteness and eigenvector relations
are propositions.

Import the installed library through `litex.config`:

```ini
[import std]
Matrix = matrix

[export]
main = "./main.lit"
```

A checkout-local project can instead use `[import]` with
`Matrix = "../../std/matrix"`, adjusting the relative path for its location.
Native operators work without an import.

## Entrywise source theorems

The following seven laws are ordinary proved source theorems. Import this
package and call them with the qualified `Matrix::main::` name; their former
bare builtin theorem names have been removed. Argument order is unchanged.

| Source theorem call | Result |
| --- | --- |
| `matrix_add_commutative(A,B,m,n)` | A+B=B+A |
| `matrix_add_associative(A,B,D,m,n)` | (A+B)+D=A+(B+D) |
| `matrix_add_zero(A,m,n)` | Both A+0=A and 0+A=A |
| `matrix_sub_self(A,m,n)` | A−A=0 |
| `matrix_scale_one(A,m,n)` | 1A=A |
| `matrix_scale_zero(A,m,n)` | 0A=0 |
| `matrix_scale_distributive(z,A,B,m,n)` | z(A+B)=zA+zB |

Here A/B/D have the same complete `matrix(C,m,n)` domain, z is complex,
and m/n are naturals including zero. Real matrix inputs are also accepted.
The proofs use entry formulas, scalar algebra and `by fn_extension`; they
do not call native matrix theorem schemas. Set-kind binders followed by exact
matrix-membership premises preserve the established matrix-first call order.

```litex
have fn A(r closed_range(1,2),c closed_range(1,3)) R=r+c
have fn B(r closed_range(1,2),c closed_range(1,3)) C=r-c+i
release thm Matrix::main::matrix_add_commutative(A,B,2,3)
matrix_add(A,B,2,3)=matrix_add(B,A,2,3)
```

See the [imported entrywise examples](../../examples/algebra/matrix_entrywise/main.lit)
for all seven laws at arbitrary dimensions and empty row/column domains.

## Native values

Dimensions are natural numbers, including zero; indices start at one.
`matrix(S,m,n)` equals `fn(r closed_range(1,m),c closed_range(1,n)) S`.
`cart_n(S,n)` is the existing `finite_seq(S,n)` space. Input domains must
match completely; restricting a wider function constructs a new function.

| Operation | Interface |
| --- | --- |
| Entrywise operations | `matrix_add(A,B,m,n)`, `matrix_sub(A,B,m,n)`, `matrix_scale(z,A,m,n)` |
| Product | `matrix_mul(A,B,m,k,n)`, with A:m×k and B:k×n |
| Matrix acting on a vector | `matrix_apply(A,v,m,n)` |
| Natural power | `matrix_power(A,n,p)` |
| Determinant and trace | `det(A,n)`, `trace(A,n)` |
| Inverse and exact rank | `matrix_inverse(A,n)`, `matrix_rank(A,m,n)` |
| Delete a row and column | `matrix_minor(A,n,i,j)` |
| Cofactor and adjugate | `matrix_cofactor(A,n,i,j)`, `matrix_adjugate(A,n)` |
| Transpose and adjoint | `transpose(A,m,n)`, `conjugate_transpose(A,m,n)` |
| Zero, identity, diagonal | `zero_matrix(m,n)`, `identity_matrix(n)`, `diagonal_matrix(v,n)` |
| Bilinear outer product | `outer_product(u,v,m,n)`, entry u(r)v(c) |
| Standard inner product | `inner_product(u,v,n)`, conjugate in u and linear in v |
| Norms | `euclidean_norm(v,n)`, `frobenius_norm(A,m,n)` |

Operations require standard R/C entries. Real input certificates refine real
outputs where applicable. Multiplication preserves factor order. Scalar
`+` and `*` retain their ordinary scalar meanings.

```litex
have fn A(r closed_range(1,2),c closed_range(1,2)) R=r+c
have fn B(r closed_range(1,2),c closed_range(1,2)) R=r-c
matrix_mul(A,B,2,2,2)(1,1)=3
matrix_mul(B,A,2,2,2)(1,1)=-3
det(A,2)=-1
det(A,2)!=0
matrix_inverse(A,2)(1,1)=-4
release thm matrix_rank_invertible(A,2)
matrix_rank(A,2,2)=2
```

Inverse formation requires a proved nonzero determinant. Given a candidate B,
prove both AB=I and BA=I, then use
`matrix_invertible_from_candidate(A,B,n)` and
`matrix_inverse_from_candidate(A,B,n)` in that order.
Rank formation requires a valid matrix; a concrete value requires proof.
`matrix_rank_from_factorization(A,U,V,L,R,m,r,n)` checks A=UV, LU=I_r,
VR=I_r, every factor's shape, and r≤m,n.

## Ordinary source definitions

Dimensions of source functions use existing templates:

| Template | Value or function |
| --- | --- |
| `\zero_vector<n>` | Zero vector in `cart_n(C,n)` |
| `\vector_add<n>(u,v)`, `\vector_sub<n>(u,v)` | Entrywise operations |
| `\vector_scale<n>(z,v)` | Scalar multiplication |
| `\row_vector<m,n>(A,r)`, `\column_vector<m,n>(A,c)` | Exact row and column restrictions |
| `\matrix_diagonal<n>(A)` | Diagonal vector |
| `\select_matrix<m,n,p,q>(A,rows,cols)` | Supplied finite index functions select entries; repetitions are allowed |
| `\matrix_kernel<m,n>(A)`, `\matrix_image<m,n>(A)` | Kernel and image sets |
| `\characteristic_polynomial<n>(A)` | The function z↦det(zI−A) |
| `\matrix_spectrum<n>(A)` | Eigenvalue set |
| `\solve_matrix<n>(A,b)` | A⁻¹b, guarded by det(A,n)≠0 |

Imported names remain qualified, for example
`\Matrix::main::solve_matrix<2>(A,b)`. Use ordinary `release obj def` when a
caller needs to unfold an imported ordinary function identifier. For the
guarded solver template, `solve_matrix_definition` exposes its equation.

The 22 ordinary predicates in [main.lit](main.lit) cover inverse candidates
and existence, rank factorization and rank candidates, symmetry, Hermitian,
orthogonal, unitary, normal, diagonal and triangular matrices, idempotence,
orthogonal projections, nilpotence, positive semidefiniteness and definiteness,
linear-system solutions, eigenpairs and eigenvalues, image membership, and
diagonalizability. Dimensions precede matrix arguments in these source props.
Orthogonal matrices are real; Hermitian and unitary matrices use C. Positive
definiteness includes self-adjointness and tests every nonzero vector.
An eigenpair requires a nonzero eigenvector.

The twenty-one checked source theorems include these seven entrywise laws,
and establish inverse-candidate uniqueness,
nonsingularity and selection; the two directions of the determinant criterion;
rank selection, uniqueness and existence; nonsingularity and inversion of
unitary matrices; and correctness and uniqueness of the guarded square-system
solution, together with the solver's defining equation. There are no source
axioms, trust statements or abstract predicates.

## Examples and boundaries

Read [matrix arithmetic](../../examples/test_objs/matrix_arithmetic.lit),
[minors and inverse](../../examples/test_objs/matrix_minors_inverse.lit),
[rectangular rank](../../examples/test_objs/matrix_rank_factorization.lit),
[complex geometry](../../examples/test_objs/finite_inner_product_norm.lit), and
[the BT contracts](../../examples/test_objs/matrix_bt_rules.lit).
[math_collections.md](math_collections.md) describes the mathematical dependencies.

Empty inner products and norms are zero; the 0×0 determinant is one. Its inverse
uses the same nonzero proof. Minors require positive order and valid deleted
indices. Cofactors and adjugates are also defined for singular matrices.
Frobenius norm is distinct from the operator norm.

Exact determinant expansion has a finite computation budget; symbolic and
larger orders remain valid objects and can use Laplace, triangular and
multiplicative theorems. This module has no floating-point rank heuristic,
automatic elimination, SVD, Jordan form, pseudoinverse or matrix exponential.
Native matrix paths currently have explicit unsupported Lean output; this
library does not claim a complete Lean translation of matrix algebra.
