# A vector space over the two-element field

The [two-element field](../two_element_field/README.md) is a vector space over
itself: vector zero, addition and scalar multiplication use the actual field's
zero, addition and multiplication. The [example](main.lit) verifies this
instance using the existing Field and VectorSpace contracts.

The identity map has image `{0,1}` and kernel `{0}`; the zero map has kernel
`{0,1}` and is not injective. The example checks those sets and obtains identity
injectivity using the existing zero-kernel criterion. It does not assume that a
zero map is injective merely because it is linear.

The one-element list containing `1` is a basis, so the space has dimension
`1`. The list containing `0` is dependent and is not a basis. These statements
use the existing finite-combination, basis and dimension interfaces and retain
the field's characteristic-two behavior.

The identity has rank `1` and nullity `0`; the zero map has rank `0` and
nullity `1`. In both cases the existing rank-nullity theorem gives their sum
as the dimension `1`. The constant-one function is explicitly shown not to
be linear, so it cannot be used with these guarded rank and nullity interfaces.

The generic identity-linearity theorem used by the example is:

```litex
thm identity_is_linear:
    ? forall K nonempty_set,F &Algebra::field::Field<K>,V nonempty_set,X &Algebra::vector_space::VectorSpace<K,F,V>:
        $Algebra::vector_space::is_linear_map(K,F,V,X,V,X,\Algebra::vector_space::identity<V>)
    release thm Algebra::vector_space::identity_linear(K,F,V,X)
```

| Location | Mathematical content |
| --- | --- |
| [main.lit](main.lit) | Actual vector-space instance, maps, kernels, basis, dimension and rank-nullity |
| [readme/main.lit](readme/main.lit) | The generic identity-linearity call above |
| [negative/expected.json](negative/expected.json) | False kernels, dimensions, ranks or nullities, and invalid maps or carriers |

The model reuses the same two-element Field; it is not a general finite-field
or vector-space construction API.
