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

The [convergence example](convergence/main.lit) also imports the public library.
It proves the negative-ratio geometric sum -1/3, the zero-ratio case and the
telescoping sum 1. It proves both the harmonic zero-term limit and its actual
nonconvergence, as well as nonconvergence of the all-one series. Further calls
cover the Cauchy equivalence, positive and absolute comparisons, zero-permitting
ratio contraction, ratio/root limit and extremum tests, and their strict
divergence directions.

The checker runs both public examples and seventeen separate rejection controls.
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
| `geometric_boundary.lit` | The geometric theorem requires `abs(r)<1` |
| `ratio_boundary.lit` | A contraction factor of 1 gives no conclusion |
| `root_boundary.lit` | A root bound of 1 gives no conclusion |
| `ratio_negative_q.lit` | The contraction factor must be nonnegative |
| `missing_ratio_nonzero.lit` | A quotient-limit test needs a genuinely nonzero tail |
| `comparison_missing_sign.lit` | Upper comparison alone does not replace `a(k)>=0` |
| `wrong_geometric_value.lit` | The negative-ratio candidate is -1/3, not 1/3 |
| `root_missing_bound.lit` | A strict q does not supply a missing root bound |
| `root_zero_index.lit` | The real root-map index must be positive |

The zero-limit converse rejection does not itself prove divergence. The
convergence example separately proves harmonic divergence using the library's
Cauchy-block argument.
`negative/context.lit` is the accepted empty module prefix; it is not a
rejection control. Run the named negative fixtures separately, not as an
ordered sequence of expected successes.
