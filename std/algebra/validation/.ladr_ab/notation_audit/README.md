# LADR notation concordance

This audit reuses the strict imported finite-tools gate; it adds no mathematical
operation or parser syntax. The consumed source and executable hashes still
match the gate's complete module snapshot.

| Source ID | Book convention | Standard-library correspondence |
| --- | --- | --- |
| 1.6 | F means R or C, and its elements are scalars | The source separates the scalar carrier K from its Field structure F. The actual pairs (R,real_field) and (C,complex_field) implement the two book choices. The generic theorem also permits other supplied Fields. |
| 1.10 | Chapter 1 fixes a positive integer n | Use the existing natural-coordinate interfaces with n in N+. Their proofs allow n in N, so restriction to positive n retains every original hypothesis. Zero dimension is an explicitly supported extension. |
| 2.1 | Lists may be written without outer parentheses | A supplied vector list is bound as vectors finite_seq(V,n) and passed directly to span and linear-combination interfaces. This is a notation correspondence, not a new unparenthesized Litex literal grammar. |

The already checked consumer uses these concrete interfaces:

```litex
? forall K nonempty_set,F &Algebra::field::Field<K>,n N:
    \Algebra::finite_span::coordinate_space<K,F,n> $in &Algebra::vector_space::VectorSpace<K,F,finite_seq(K,n)>
```

It also instantiates actual real and complex fields, typed vector lists, finite
coordinates and zero-length lists. The full imported gate accepts 66 statements;
its four refusal controls are retained evidence from the preceding increment.
Run the [finite-space checker](../finite_tools/check.py) to verify those
executable consumers with the current release binary.

Item 1.8 is independently deferred. This notation audit does not prove equality
of the complete input domains of two equal function objects, or equality of
arbitrary list lengths from raw function equality.

