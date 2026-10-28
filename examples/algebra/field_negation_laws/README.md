# Field negation laws

Negation distributes over addition, and changing the sign of one factor
changes the sign of a product. Both factors may be zero:

```litex
thm product_with_negative:
    ? forall K nonempty_set,F &Algebra::field::Field<K>,a,b K:
        F.mul(a,F.neg(b))=F.neg(F.mul(a,b))
    release thm Algebra::field::mul_neg(K,F,a,b)
```

The same library provides the corresponding rule for a negative left factor,
the product of two negatives, and uniqueness of an additive inverse. The
[real-field example](main.lit) checks zero operands and concrete values such as
`3*(-4)=-12` and `(-3)*(-4)=12`.

| Location | Mathematical content |
| --- | --- |
| [main.lit](main.lit) | Real values and zero operands |
| [contracts/main.lit](contracts/main.lit) | Five generic signatures |
| [readme/main.lit](readme/main.lit) | The generic negative-product example above |
| [negative/expected.json](negative/expected.json) | Incorrect signs, missing inverse premise and invalid signatures |

All results use the existing Field operations; no multiplicative inverse or
nonzero assumption is needed.
