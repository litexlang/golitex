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

The downstream use specializes the general result to `n = 100`, showing that
the first 100 positive odd integers sum to `10000`.

The Litex source itself also records the smaller concrete consequence
`sum(1, 10, kth_odd) = 10^2 = 100`. It is obtained from the universal theorem
by automatic matching, not by a separate step lemma or explicit theorem call.
