# Zero products in a field

In an arbitrary field, a product is zero exactly when at least one of its
factors is zero. A nonzero product therefore has two nonzero factors. These
results use the supplied Field operations and make no order or characteristic
assumption. The generic consumer is:

```litex
thm consume_zero_product_factors:
    ? forall K nonempty_set,F &Algebra::field::Field<K>,a,b K:
        F.mul(a,b)=F.zero
        =>:
            a=F.zero or b=F.zero
    release thm Algebra::field::zero_product_factors(K,F,a,b)
```

The [two-element-field example](main.lit) checks zero and nonzero products using
the actual characteristic-two model. In particular, `0*1=0` while `1!=0`, so
a zero product does not force both factors to vanish. The [real-field caller]
(real/main.lit) checks both zero and nonzero cases; [contracts](contracts/main.lit)
exercise all three results over arbitrary fields.

The [negative controls](negative/expected.json) cover missing zero or nonzero
assumptions, the false both-factors-zero claim and incorrect carriers. Run
`python3 examples/algebra/field_zero_product/check.py --binary /path/to/litex
--output-dir /path/to/results` for source, consumer and installed checks.
