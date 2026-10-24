# Matrices as functions

This short chapter studies one family of real matrices,

$$
A(t)=\begin{pmatrix}t+2&t+3\\t+3&t+4\end{pmatrix},\qquad t\in\mathbb R.
$$

A matrix-valued function is still an ordinary function in Litex. Its values
can be called at two indices, used to construct vectors, and passed to native
matrix operations. The chapter follows these uses through one definition. Its central result is a
determinant that stays constant as the matrix entries change.

Read [main.lit](main.lit) in order. It requires no imports.

## From entries to an invariant

The function `family` returns the matrix determined by `t`. The proof exposes
its four entries and the two products in the determinant formula. Their
difference is the polynomial identity

$$
(t+2)(t+4)-(t+3)^2=-1.
$$

```litex
have fn family(t R) matrix(R,2,2)=fn(r closed_range(1,2),c closed_range(1,2)) R {t+r+c}

claim:
    ? forall t R:
        det(family(t),2)=-1
    family(t)(1,1)=t+2
    family(t)(1,2)=t+3
    family(t)(2,1)=t+3
    family(t)(2,2)=t+4
    family(t)(1,1)*family(t)(2,2)=(t+2)*(t+4)
    family(t)(1,2)*family(t)(2,1)=(t+3)*(t+3)
    det(family(t),2)=(t+2)*(t+4)-(t+3)*(t+3)=-1
```

This proves the value for every real parameter. The following claim in the
chapter reuses that universal equality to establish that the determinant is
always nonzero. The trace, by comparison, takes the values 6 and 8 at parameters
0 and 1.

## From a matrix to a vector

The call `family(t)(r,c)` first selects a matrix, then selects its entry. A row
is constructed by fixing one of those two indices:

```litex
have fn family(t R) matrix(R,2,2)=fn(r closed_range(1,2),c closed_range(1,2)) R {t+r+c}
have fn first_row(t R) cart_n(R,2)=fn(c closed_range(1,2)) R {family(t)(1,c)}

first_row(0)(2)=3
```

The returned row has carrier `cart_n(R,2)`, which is the same finite-function
space as `finite_seq(R,2)`. The matrix retains its two-index call, while the
explicit row construction supplies a one-index call.

## Equalities of whole functions

Since swapping the two indices preserves `t+r+c`, the chapter proves
`transpose(family(t),2,2)=family(t)` for every real `t` using function
extensionality. After viewing the same real matrix over the complex numbers,
it proves the corresponding conjugate-transpose equality. The pointwise proof
uses the real codomain to justify that conjugation leaves each entry fixed.

The last two lines extend the discussion to an empty matrix: its determinant
is 1 and its trace is 0. The dimensions remain explicit even when there are no
entries to inspect.

## Reading map and scope

| Section in main.lit | Mathematical step |
| --- | --- |
| 1 | The exact finite function space behind `matrix(S,m,n)` |
| 2 | A matrix-valued parameter function and its first-row vector |
| 3 | Constant determinant and its nonzero consequence |
| 4 | Two concrete diagonal sums |
| 5 | Symmetry, scalar inclusion and self-adjointness as function equalities |
| 6 | Empty determinant and empty trace conventions |

The source is checked in strict mode and contains no user assumptions, axioms
or abstract predicates. It relies on Litex's verifier and native mathematical
rules. Its determinant computation uses orders 2 and 0; its trace claims are
the two concrete values above. General elimination, inverse construction and
rank are outside this chapter. Lean compilation of the native matrix paths
is currently unsupported.

[math_collections.md](math_collections.md) describes the mathematical interfaces;
[litex.config](litex.config) exports the chapter as `main`.
