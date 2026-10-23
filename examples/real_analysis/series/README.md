# Ordered real series examples

[main.lit](main.lit) imports [std/real_series](../../../std/real_series/README.md)
and explicitly releases its four source function definitions. It proves the
zero series, a real geometric series and a finite change, then uses the linear,
finite-support and necessary zero-term rules. It accepts both complete
`seq(R)` and `fn(k N+) R` inputs.

The geometric proof first establishes `(1/2)^n -> 0` and
`partial_sum(geometric,n)=1-(1/2)^n`. It proves the series candidate `1`
before selecting the sum. Changing the first term from `1/2` to `3/2` gives
the candidate `1-1/2+3/2=2`, followed by the selected value `2`.

```bash
LITEX_STD_PATH="$PWD/std" target/release/litex -lang en -strict -f examples/real_analysis/series/main.lit
python3 examples/real_analysis/series/check.py
```

The checker runs the public example and eight separate rejection controls.
Every rejection must occur in the final statement, with its complete prefix
accepted and no session termination:

| Fixture in `negative/` | Required rejection |
| --- | --- |
| `missing_convergence.lit` | Selecting a sum before convergence evidence |
| `lim_missing_convergence.lit` | Selecting the partial-sum limit before convergence evidence |
| `eliminated_selector.lit` | Multiplying by zero still checks the sum's guard |
| `wrong_candidate.lit` | A wrong candidate after proving the zero candidate |
| `zero_prefix.lit` | Prefix length zero is outside `N+` |
| `incomplete_sequence.lit` | A finite tuple is not a complete real sequence |
| `wrong_finite_correction.lit` | Equal tails do not make different finite-prefix sums equal |
| `incorrect_zero_converse.lit` | A zero term limit supplies no converse series theorem |

The last rejection does not itself prove the divergence of a particular
series. Harmonic divergence and general convergence tests remain later work.
`negative/context.lit` is the accepted empty module prefix; it is not a
rejection control. Run the named negative fixtures separately, not as an
ordered sequence of expected successes.
