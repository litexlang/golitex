# Field distributivity and differences

The field interface derives right distributivity from its existing left
distributivity and commutative multiplication. It represents the difference
`b-c` as `F.add(b,F.neg(c))`; multiplication distributes over that expression:

```litex
thm product_of_difference:
    ? forall K nonempty_set,F &Algebra::field::Field<K>,a,b,c K:
        F.mul(a,F.add(b,F.neg(c)))=F.add(F.mul(a,b),F.neg(F.mul(a,c)))
    release thm Algebra::field::mul_difference(K,F,a,b,c)
```

The opposite multiplication order is also available. A difference is zero
exactly when its two operands are equal, expressed as two source theorems.
All operands may be zero. The [real-field example](main.lit) checks
`4*(3-2)=4`, `(3-2)*4=4` and `(2+3)*4=20`.

| Location | Mathematical content |
| --- | --- |
| [main.lit](main.lit) | Real values, equal operands and zero operands |
| [contracts/main.lit](contracts/main.lit) | Five generic signatures |
| [readme/main.lit](readme/main.lit) | The generic product-of-difference example above |
| [negative/expected.json](negative/expected.json) | False values, missing premises and invalid signatures |

No new subtraction operation is introduced. These statements require only
Field's existing laws, with no restriction on characteristic.
