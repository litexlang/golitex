# A certified matrix solve

This chapter solves

$$
\begin{pmatrix}2&3\\3&4\end{pmatrix}x=
\begin{pmatrix}1\\0\end{pmatrix}.
$$

The determinant is −1. After proving it is nonzero, the chapter constructs
the inverse-based solution, checks both coordinates, and finds its Euclidean
norm: x=(-4,3), ‖x‖₂=5. It proves that every solution equals this one, that
the coefficient matrix has rank two, and that it is symmetric.

Read [main.lit](main.lit). Its matrix values remain ordinary two-index
functions and its solution remains an ordinary one-index function.
[litex.config](litex.config) imports the source library [std/matrix](../../std/matrix/README.md)
as `Matrix`.

```litex
have fn system(r closed_range(1,2),c closed_range(1,2)) R=r+c
det(system,2)=-1
det(system,2)!=0
have displacement cart_n(C,2)=matrix_apply(matrix_inverse(system,2),(1,0),2,2)
displacement(1)=-4
displacement(2)=3
euclidean_norm(displacement,2)=5
```

The complete chapter establishes Ax=b using the inverse identities and
matrix-action composition. It then applies the library's proved
`invertible_matrix_solution_unique`. Symmetry is a library proposition proved
by ordinary function extensionality.

The final section uses `\Matrix::main::solve_matrix<2>` and its public
`solve_matrix_definition` theorem to identify the library value with the
native construction and compute its coordinates. The determinant proof is
needed for both interfaces.

This example has no source axioms or trust statements. It relies on Litex's
native matrix and scalar rules; native matrix Lean output remains unsupported.
It illustrates a certified square solve. Rank factorization for a nonzero
rectangular matrix is in [this separate example](../../examples/test_objs/matrix_rank_factorization.lit).
