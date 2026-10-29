# Alternating series

The example imports `real_series` and proves that the ordered alternating
harmonic series, `a(k)=(-1)^(k+1)/k` for `k in N+`, converges while its
absolute-value series diverges. It also exercises the zero sequence, including
a non-strictly decreasing magnitude. The convergence theorem does not compute
the sum. The example also checks the next-term remainder bounds at n=1, 2, and
3 for an actual sum witness.

The negative files omit the zero limit, monotonicity, the odd-term sign law,
or the candidate sum needed for a remainder estimate, respectively. Each must
reject the final attempted theorem application at its premise while earlier
statements remain accepted.
Run the strict positive and negative checks from the repository root:

```bash
python3 examples/real_analysis/series/alternating/check.py
```

The example applies the first remainder theorem directly, then computes the
partial sums and next-term magnitudes to expose concrete numerical bounds.
