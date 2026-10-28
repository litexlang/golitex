# Zero-coefficient field equations

A zero-coefficient linear equation `0*x=b` has no solution when `b` is
nonzero. When `b=0`, every field element is a solution; in particular, zero
and one are distinct solutions:

```litex
thm two_solutions_when_coefficient_is_zero:
    ? forall K nonempty_set,F &Algebra::field::Field<K>:
        exist x,y K st {x!=y,F.mul(F.zero,x)=F.zero,F.mul(F.zero,y)=F.zero}
    release thm Algebra::field::field_zero_linear_two_solutions(K,F)
```

For `0*x+b=c`, every element is a solution when `b=c`, while no element is a
solution when `b!=c`. The [real-field example](main.lit) checks both cases and
explicitly checks zero and one as different solutions.

| Location | Mathematical content |
| --- | --- |
| [main.lit](main.lit) | Real zero-coefficient linear and affine cases |
| [contracts/main.lit](contracts/main.lit) | Five generic signatures |
| [readme/main.lit](readme/main.lit) | Two distinct solutions for the zero linear equation |
| [negative/expected.json](negative/expected.json) | False values, missing inequalities and invalid signatures |

The no-solution laws quantify over a candidate `x` and prove it cannot satisfy
the equation. They use no inverse of zero or new solution operation.
