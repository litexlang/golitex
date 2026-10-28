# Guarded field inverse laws

Multiplicative inversion is defined on nonzero field elements. The inverse of
one is one:

```litex
thm inverse_of_one:
    ? forall K nonempty_set,F &Algebra::field::Field<K>:
        F.inv(F.one)=F.one
    release thm Algebra::field::field_inverse_one(K,F)
```

The field library also proves that the inverse of a nonzero element is nonzero,
that taking its inverse twice returns the original, that its inverse is unique,
and that the inverse of a product of nonzero elements is the product of their
inverses. These laws retain their natural nonzero hypotheses.

For the generic product identity, the caller first publishes the existing
`nonzero_product` result in its context, so the product is known to lie in the
inverse operation's domain. The real caller likewise releases that result for
`2` and `3` before the product-inverse call. This is domain evidence for the
existing operation, not an extra hypothesis on the theorem.

A generic nested-inverse statement likewise first publishes the existing
`nonzero_field_inverse` consequence in the caller's context. Its natural
premise remains that the original element is nonzero.

| Location | Mathematical content |
| --- | --- |
| [main.lit](main.lit) | Real inverse values, including `inv(2*3)=1/6` |
| [contracts/main.lit](contracts/main.lit) | Five generic signatures and product-domain evidence |
| [readme/main.lit](readme/main.lit) | The generic inverse-of-one example above |
| [negative/expected.json](negative/expected.json) | Zero arguments, missing premises, false values and invalid signatures |

There is no selected inverse of zero or new division operation.
