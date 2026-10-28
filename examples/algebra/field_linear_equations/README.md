# Linear and affine equations over a field

For a nonzero coefficient, a linear equation has a unique solution. The same
is true of an affine equation:

```litex
thm unique_affine_solution:
    ? forall K nonempty_set,F &Algebra::field::Field<K>,a,b,c K:
        a!=F.zero
        =>:
            exist! x K st {F.add(F.mul(a,x),b)=c}
    release thm Algebra::field::field_affine_equation_unique(K,F,a,b,c)
```

The solution of `a*x=b` is `inv(a)*b`; that of `a*x+b=c` is
`inv(a)*(c-b)`, where `c-b` uses the existing addition and negation operations.
The [real-field example](main.lit) checks `2*x=6` with `x=3` and
`2*x+3=7` with `x=2`.

The coefficient hypothesis matters: for `0*x=0`, both `x=1` and `x=2` are
solutions, so uniqueness fails. The example checks this boundary directly.

| Location | Mathematical content |
| --- | --- |
| [main.lit](main.lit) | Real linear and affine solutions and zero-coefficient boundaries |
| [contracts/main.lit](contracts/main.lit) | Four generic signatures |
| [readme/main.lit](readme/main.lit) | The generic affine unique-existence example above |
| [negative/expected.json](negative/expected.json) | Zero coefficients, wrong solutions, missing premises and invalid signatures |

The theorems do not select a new solution operation or define inverse at zero.
