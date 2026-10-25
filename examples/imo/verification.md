# Verification of the collected IMO proofs

Checked on 2026-10-25. This task reorganizes sources; it does not repair proofs.

The release binary SHA-256 was `10c5e5c8adac38794e6c49b7a29a8d161580675199fc85beb443b4fdb4604bda` and remained unchanged during the gates.

All five inequalities, all nine miniF2F files, IMO 1972 P5 and two representative
geometry targets were checked at their new paths: **9 strict passes and 8 failures**.
The other **13 geometry solution packages were not rerun** in this organization task.
Their source bytes and export order are unchanged; earlier strict verification is
documented in the [historical showcase repair report](../../showcases/verification_runs/2026-10-14-showcase-repair.md).

## Current checks

| Target | Result | First rejected obligation, if any |
| --- | --- | --- |
| [functional_equations/imo_1972_p5.lit](functional_equations/imo_1972_p5.lit) | fail | `(abs (f(x)) * (2 * abs (g(y)))) = abs (((2 * f(x)) * g(y)))` |
| [geometry/imo_1960_p3/Solution-1/solution.lit](geometry/imo_1960_p3/Solution-1/solution.lit) | pass | — |
| [geometry/imo_1966_p6/solution.lit](geometry/imo_1966_p6/solution.lit) | pass | — |
| [inequalities/imo_1983_p6.lit](inequalities/imo_1983_p6.lit) | pass | — |
| [inequalities/imo_1995_p2.lit](inequalities/imo_1995_p2.lit) | pass | — |
| [inequalities/imo_2001_p2.lit](inequalities/imo_2001_p2.lit) | pass | — |
| [inequalities/imo_2005_p3.lit](inequalities/imo_2005_p3.lit) | pass | — |
| [inequalities/imo_2006_p3.lit](inequalities/imo_2006_p3.lit) | pass | — |
| [minif2f/imo_1959_p1.lit](minif2f/imo_1959_p1.lit) | fail | `((21 * n) + 4) != 0` |
| [minif2f/imo_1960_p2.lit](minif2f/imo_1960_p2.lit) | fail | `s != 1` |
| [minif2f/imo_1961_p1.lit](minif2f/imo_1961_p1.lit) | fail | `0 < ((((x - y) ^ 2) + ((y - z) ^ 2)) + ((z - x) ^ 2))` |
| [minif2f/imo_1962_p2.lit](minif2f/imo_1962_p2.lit) | fail | `(((3 - x) - (x + 1)) - (1 / 4)) > (((((x + 1) + B) + (1 / 4)) - (x + 1)) - (1 / 4))` |
| [minif2f/imo_1964_p1_1.lit](minif2f/imo_1964_p1_1.lit) | fail | `exist! q Z st {a = ((d * q) + (a % d))}` |
| [minif2f/imo_1964_p1_2.lit](minif2f/imo_1964_p1_2.lit) | fail | `exist! q Z st {a = ((d * q) + (a % d))}` |
| [minif2f/imo_1964_p2.lit](minif2f/imo_1964_p2.lit) | pass | — |
| [minif2f/imo_1966_p5.lit](minif2f/imo_1966_p5.lit) | fail | `((((a(1) - a(2)) * x(2)) + ((a(1) - a(3)) * x(3))) + ((a(1) - a(4)) * x(4))) = 1` |
| [minif2f/imo_1973_p3.lit](minif2f/imo_1973_p3.lit) | pass | — |

The two geometry gates cover a multi-file ordered package (1960 P3, Solution 1)
and a self-contained solution (1966 P6). The inequalities all remain strict passes.

For 1972 P5, the current file rejects the product step:

```text
abs(f(x)) * (2 * abs(g(y))) = abs(2 * f(x) * g(y))
```

Its earlier local success capture contains a different, longer proof. It is not
evidence that this current file passes. The source is retained without adding trust.

## Organization acceptance

- Every collected `.lit` and all 15 geometry configs match their original hashes.
- All geometry export targets exist and retain their original order.
- Local experiment originals and existing nested Git repositories are preserved.
- Original showcase indexes redirect to this collection; historical captures retain the commands that were actually run.
- No kernel, theorem statement or proof body changed.
- No Cargo, Lean, full-release or local textbook gate was run.

[verification.json](verification.json) records exact commands, parsed envelopes,
rejections, source hashes and config order. A pass requires exit 0, `kind: run`,
`run_result: success`, `session_terminated: false` and `termination: null`.
The collection manifest records the unexecuted geometry targets as `not_rerun`.

[Combined index](README.md)
