# Natural Mathematics

For every integer `n ≥ 1`, the sum of the first `n` positive odd integers is
`n²`:

```text
1 + 3 + 5 + ⋯ + (2n - 1) = n².
```

Write the `k`-th positive odd integer as `kth_odd(k) = 2k - 1`. The induction
base is the calculation `kth_odd(1) = 1`, hence the one-term sum is `1 = 1²`.

For the induction step, split off the last term:

```text
sum(1, n + 1, kth_odd)
  = sum(1, n, kth_odd) + kth_odd(n + 1)
  = n² + (2(n + 1) - 1)
  = (n + 1)².
```

## The property viewpoint

The equality is more useful when it can be packaged behind a reusable
mathematical interface. Define `is_square_of(value, root)` to mean
`value = root²`. This is a relation: the root is supplied explicitly, so a
caller can retain the witness and use it in later arguments.

There are then three separate mathematical moves:

1. Every `value` that is `is_square_of(value, root)` is nonnegative, because
   `root² ≥ 0`.
2. The odd sum is `is_square_of(sum(1, n, kth_odd), n)`, by the established
   identity `sum(1, n, kth_odd) = n²`.
3. Composing the first two facts gives
   `sum(1, n, kth_odd) ≥ 0`.

This separation is the important part of the example: the induction proves
one equality, while the property becomes a reusable interface that can have
many constructors and many consumers.

The downstream use specializes the general result to `n = 100`, showing that
the first 100 positive odd integers sum to `10000`. It also retains an
`IsSquareOf` certificate and obtains nonnegativity through the general
property law.

The Litex source itself also records the smaller concrete consequence
`sum(1, 10, kth_odd) = 10^2 = 100`. It is obtained from the universal theorem
by automatic matching, not by a separate step lemma or explicit theorem call.
