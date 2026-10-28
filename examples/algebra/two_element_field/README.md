# A two-element field

This example constructs a field on `{0,1}` with addition modulo two,
multiplication, and additive inverse equal to the element itself. In this
field, `1+1=0`; field zero and one remain distinct. Its multiplicative inverse
is defined only for nonzero elements, so the only permitted input is `1`.

The [model](model.lit) checks its operation tables and all Field axioms by
explicit finite cases, constructs the existing `Algebra::field::Field` instance,
and exercises inverse, distributivity and linear-equation laws. The
[cross-file caller](main.lit) imports the same named instance facts and reuses
the generic laws. No Field axiom or native rule is added.

For a generic double-inverse statement, publish the existing nonzero-inverse
fact first so the nested inverse's domain is available to the caller:

```litex
claim:
    ? forall K nonempty_set,F &Algebra::field::Field<K>,a K:
        a!=F.zero
        =>:
            F.inv(a)!=F.zero
    release thm Algebra::field::nonzero_field_inverse(K,F,a)

thm inverse_twice_in_any_field:
    ? forall K nonempty_set,F &Algebra::field::Field<K>,a K:
        a!=F.zero
        =>:
            F.inv(F.inv(a))=a
    release thm Algebra::field::field_inverse_involution(K,F,a)
```

| Location | Mathematical content |
| --- | --- |
| [model.lit](model.lit) | Two-element operations, all Field axioms, characteristic-two values and generic applications |
| [main.lit](main.lit) | Cross-file reuse of the actual Field instance |
| [readme/main.lit](readme/main.lit) | The generic guarded inverse example above |
| [negative/expected.json](negative/expected.json) | False values, inverse at zero, invalid carrier and missing premises |

This is one concrete finite field, not a general finite-field construction.
