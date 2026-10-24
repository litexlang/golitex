# Mathematical interfaces

This chapter connects an indexed formula, its matrix invariants and its
function equalities. All matrix vocabulary is native; the two named functions
are source-level constructions used by the chapter.

## Finite function spaces

For a set S and natural dimensions m,n, matrix(S,m,n) is the exact space
`fn(r closed_range(1,m),c closed_range(1,n)) S`. Natural dimensions include
zero; both index ranges start at 1. The declared complete domains matter:
a function on all positive integer pairs needs an explicit restriction before
it supplies a matrix of a fixed nonempty size.

A matrix has two arguments in one application layer, `M(r,c)`. A row has one.
`cart_n(R,2)` reuses `finite_seq(R,2)`, the one-argument finite function space.
These call protocols explain why the chapter constructs its row explicitly.

## The parameter family and its row

`family(t R) matrix(R,2,2)` has the formula `t+r+c` at entry (r,c).
The parameter ranges over R, while the two indices range over {1,2}.
The value `family(t)` is itself callable.

`first_row(t R) cart_n(R,2)` fixes the row index of that same matrix at 1.
The construction consumes the matrix's actual finite domain and real return
carrier. It does not introduce a second representation of matrix values.

## Invariants as facts

The determinant is a scalar construction `det(family(t),2)`. The source
proves its value -1 for every real t by substituting the four entries into
the two products of the 2x2 definition. A subsequent local claim instantiates
that universal value to prove a nonzero determinant. It constructs no inverse.

`trace(family(0),2)=6` and `trace(family(1),2)=8` give concrete diagonal sums.
The chapter does not claim a checked universal trace formula.

Symmetry and self-adjointness are stated directly as equalities between
`transpose`/`conjugate_transpose` and the supplied function value. Their proofs
use function extensionality. The self-adjoint argument retains the real
carrier of each entry before applying conjugation's real-value law.
No new symmetry predicate or native Fact is declared.

## Empty domains

`zero_matrix(0,0)` supplies an empty matrix. The determinant convention
gives 1, and the empty diagonal sum gives trace 0. Explicit dimensions are
retained because function values on empty domains do not in general determine
a unique rectangular shape.

The chapter reuses native definitions and rules. It adds no Obj/Fact shape,
reserved builtin theorem, kernel strategy, user axiom or abstract predicate.
