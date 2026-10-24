# Mathematical interfaces

[main.lit](main.lit) defines the real coefficient function
`system(r,c)=r+c` on I₂×I₂ and proves det(system,2)=−1.

The selected inverse is used only after det≠0. The native construction
`matrix_apply(matrix_inverse(system,2),(1,0),2,2)` is the solution vector.
Its two coordinates and norm are proved exactly. Matrix-action composition
and the inverse identities establish the ordinary relation
`Matrix::main::solves_matrix_system`; the imported source theorem proves
uniqueness over the complete space `cart_n(C,2)`.

The remaining facts are full rank, symmetry as a source proposition, and
agreement with the guarded source function `\Matrix::main::solve_matrix<2>`.
The latter uses its proved defining equation. No additional native Obj, Fact,
predicate, rule or theorem is introduced by this showcase.
