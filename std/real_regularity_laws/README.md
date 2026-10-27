# Regularity of real linear combinations

This optional source module imports real_multivariable, real_higher_order_laws
and real_regularity. Import it as `RegLaws = real_regularity_laws`; all four
source theorems are in RegLaws::main. The base regularity module does not import
this law layer.

`unary_c_k_linear_combination(D,k,f,g,h,a,b)` consumes C^k of f and g on the same
actual open D⊆R and h(x)=a*f(x)+b*g(x) on D. It proves C^k of h. The independent
`scalar_c_k_linear_combination(n,D,k,f,g,h,a,b)` has one vector input in an actual
open D⊆cart_n(R,n) and real output. Both include k=0 and real coefficients.
The supplied formula describes the complete function h on D.

`unary_smooth_linear_combination(D,f,g,h,a,b)` and
`scalar_smooth_linear_combination(n,D,f,g,h,a,b)` consume the corresponding
smoothness of both inputs and the same formula. Their proofs apply finite
regularity closure at every order. No new function or selector is introduced.

The proofs combine explicit derivative candidates, then prove continuity of the
canonical derivative functions on exactly D. The scalar proof explicitly
materializes the existing native Euclidean neighborhood from source openness
before applying constant-expression continuity. It does not reinterpret the
domain as the full coordinate space. Coefficients of zero do not remove the
stated input regularity premises.

There are four source thms, with no trust, axioms, AST, native BT, automatic
strategy or runtime change. Product, quotient and composition closure are
outside this package. Actual imports, examples and focused boundaries are
recorded in the maintained local native-analysis inventory.
