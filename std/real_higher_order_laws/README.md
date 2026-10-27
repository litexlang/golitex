# Finite higher derivative laws

This optional source module proves linearity for unary real finite-order derivatives
and ordered real partial derivatives with one vector input. Import it explicitly
alongside `real_multivariable`; no native theorem, selector or strategy is added.
The source proofs, actual package imports and installed CLI callers passed
focused acceptance, including twelve refusal-and-liveness controls.

```toml
[import std]
Calc = real_multivariable
Higher = real_higher_order_laws
```

The namespace is `Higher::main`. The unary interfaces are
`nth_derivative_linear_combination(D,k,f,g,h,p,a,b,A,B)`,
`nth_derivative_add(D,k,f,g,h,p,A,B)`,
`nth_derivative_subtract(D,k,f,g,h,p,A,B)` and
`nth_derivative_scale(D,k,f,h,p,a,A)`. Supply each input candidate and the
pointwise formula for h. Their conclusions are candidates; use the original
candidate-existence and value theorems before selecting a numeric derivative.

The independent ordered interfaces are
`ordered_partial_linear_combination(n,D,k,f,g,h,p,path,a,b,A,B)`,
`ordered_partial_add(n,D,k,f,g,h,p,path,A,B)`,
`ordered_partial_subtract(n,D,k,f,g,h,p,path,A,B)` and
`ordered_partial_scale(n,D,k,f,h,p,path,a,A)`. All functions share the same
complete actual input domain D. The path is finite and ordered; it is never
sorted, reinterpreted as coordinate counts or shared with the unary contract.

Both families include k=0. Their proofs intersect the supplied certificates'
intermediate domains and use a positive common neighborhood at each step.
The lower-level `real_derivatives_linear_combination/12` and
`real_partials_linear_combination/14` expose the corresponding first-order law
on a supplied common target domain and radius. There are ten source theorems,
with no source trust or axioms. Products, quotients, compositions, smoothness
classes and mixed-partial exchange are outside this module.
