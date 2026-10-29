# Riemann integral absolute bounds

This strict imported example proves the bound for `f(x)=-x` on `[0,1]` using
the exact values `-1/2` and `1/2`, then checks reversed and equal endpoints.
It also uses functions whose complete domain is exactly `[0,1]`, invokes
the continuous-function integrability variant, and checks the difference
bound for `x^2` and `x` in both directions. Four negative controls omit an
absolute-value candidate, omit its pointwise formula, try the forward
inequality with reversed endpoints, or omit the absolute-difference candidate.

```bash
python3 examples/real_analysis/integral_absolute_bound/check.py
```
