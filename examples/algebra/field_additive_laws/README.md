# Elementary field additive laws

The field interface provides additive identity, inverse and cancellation laws.
Cancellation needs equality of the two sums; it does not require a nonzero
summand. Negating an element twice returns that element:

```litex
thm negating_twice:
    ? forall K nonempty_set,F &Algebra::field::Field<K>,a K:
        F.neg(F.neg(a))=a
    release thm Algebra::field::neg_involution(K,F,a)
```

The [real-field example](main.lit) exercises both cancellation directions,
zero's additive inverse and double negation. The generic contracts keep the
sum-equality premise for cancellation.

| Location | Mathematical content |
| --- | --- |
| [main.lit](main.lit) | Real field values and cancellation calls |
| [contracts/main.lit](contracts/main.lit) | Six generic signatures |
| [readme/main.lit](readme/main.lit) | The generic double-negation example above |
| [negative/expected.json](negative/expected.json) | False or missing equalities, wrong values and invalid signatures |

The laws use the existing Field operations and do not introduce a new group
conversion or coercion hierarchy.
