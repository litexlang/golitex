# Real three-dimensional cross products

Import `real_multivariable` as `vectors`; use the `cross_product` export.
`real_cross_product(u,v)` takes two members of `cart_n(R,3)` and returns one.
It uses right-handed Cartesian coordinates, preserves magnitudes, and accepts
zero vectors. The equivalent complete `fn(k closed_range(1,3)) R` is accepted.
It is a total source construction, so no existence or candidate prop is needed.

The [main example](main.lit) proves e1×e2=e3, the reverse sign, a cyclic basis
product and a product of explicitly indexed functions. It calls the general
source theorems for self/zero products, anticommutativity, both sides of
bilinearity, orthogonality, the Lagrange and norm-square identities, and both
triple-product identities. The determinant theorem requires a supplied matrix
whose columns are the three input vectors in that order.

Concrete examples publish their coordinate equalities before using
`real_cross_product_value(u,v,a,b,c)`. The known mixed-coordinate
`release tuple def (1,0,0)` return-bound failure remains outside this feature.
No trust, axiom, new native operator, BT or automatic strategy is added.
This cross product has a separate contract from the native three-dimensional
field operation `curl(F,p)`; it does not assert associativity or provide a
complex or arbitrary-dimensional cross product.

Run the example and focused rejection controls:

```bash
python3 examples/real_analysis/multivariable/cross_product/check.py
```

The checker verifies the saved example and opens a persistent Session. It
introduces a fresh concrete basis fixture in that live Session, respecting
export-file fact scoping. Its nine rejection turns retain that same context.
Wrong dimension, complex input, wrong complete index domain, wrong
arity, coordinate 4, reversed orientation, an incorrect supplied value,
incorrect determinant columns and false associativity must all reject.
The accepted context is checked again after those failures.
