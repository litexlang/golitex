# Elementary field multiplication laws

For every field in the algebra package, multiplication by zero gives zero.
A nonzero factor can be cancelled on either side; consequently, if a product
is zero and one factor is nonzero, the other is zero. Two nonzero factors
have a nonzero product:

```litex
thm nonzero_factors_have_nonzero_product:
    ? forall K nonempty_set,F &Algebra::field::Field<K>,a,b K:
        a!=F.zero
        b!=F.zero
        =>:
            F.mul(a,b)!=F.zero
    release thm Algebra::field::nonzero_product(K,F,a,b)
```

The [real-field example](main.lit) checks these calls and exhibits the
boundary: `0*1=0*2` while `1!=2`, so cancellation needs a nonzero factor.
The inverse operation remains defined only away from zero.

| Location | Mathematical content |
| --- | --- |
| [main.lit](main.lit) | Real field values and the zero-factor boundary |
| [contracts/main.lit](contracts/main.lit) | All seven generic signatures |
| [readme/main.lit](readme/main.lit) | The generic nonzero-product example above |
| [negative/expected.json](negative/expected.json) | Missing guards, invalid inverse and false values |

These laws do not introduce a ring hierarchy or a new field construction.
