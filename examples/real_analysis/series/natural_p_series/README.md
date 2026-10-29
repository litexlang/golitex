# Reciprocal series with natural exponents

This example imports `real_series` and proves convergence for `1/k^2` and
`1/k^3`, as well as divergence at exponents 0 and 1. The new theorem covers
natural exponents `p>=2`; it neither computes a sum nor covers arbitrary real
exponents. The negative controls try the p>=2 theorem at p=1 and p=0, whose
premise and argument type respectively must be rejected.

Run the strict positive and negative checks from the repository root:

```bash
python3 examples/real_analysis/series/natural_p_series/check.py
```
