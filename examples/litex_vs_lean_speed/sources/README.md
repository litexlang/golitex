# Comparison sources

Litex and Lean sources for each case, grouped by batch and domain. The recorded
validation ran each `.lit` file independently with release
`target/release/litex -f`, returning `run_result: success`.

| Directory | Contents | Source batch |
| --- | --- | --- |
| `arithmetic/` | Natural-number addition and real square roots | 2026-10-22 arithmetic and radicals |
| `sums/` | Interval sums, finite-set sums, concrete trigonometric values and identities | 2026-10-22 finite sums and trigonometry |
| `elementary/` | Primality, gcd, factorials, large fourth-power identities, logarithms and radical products | 2026-10-22 elementary calculations and number theory |
| `quantifiers/` | Universal facts, witnesses, unique existence and existence elimination (21 cases, multiple Lean routes) | 2026-10-23 quantifiers |
| `declarations/` | Functions, predicates, piecewise definitions, recursion, structures, named theorems, contradiction, cases and induction | 2026-10-23 definitions and proof commands |
| `new-round/` | Sets, functions, integer arithmetic, divisibility, finite combinatorics, calculus, Cartesian products and √2 irrationality | 2026-10-23 additional domains |
| `multi-step/` | Inequalities, algebraic cancellation, divisibility, existence construction and arithmetic, without matching-theorem reuse in Lean | 2026-10-23 second round |
| `statement-forms/` | Predicate definitions and witnesses, witness extraction, an ε-N limit problem and set-equality obligations | 2026-10-23 third round |
| `type-bridge/` | Conversion annotations, bridge automation and direct lemmas for the same Lean statement, plus two corresponding Litex arithmetic statements | 2026-10-24 type-bridge component experiment |
| `quantitative-iteration/` | Parametric Newton step, quadratic gradient descent and perturbed geometric recurrence; complete sources for both systems and mathematical design | 2026-10-24 whole-process measurements |
| `lean-proof-pipeline/` | Actual Lean proof terms, explicit arguments and raw `Expr` for `1 + 1 = 2` and parametric addition of one | 2026-10-24 explanatory experiment, no timing |
| `search-expansion/` | Shifted sums with 16/64/128 terms; a quadratic inequality with 0/12/24 irrelevant hypotheses; all timing directions and direct Lean baselines retained | 2026-10-24 separate checking-path batch |

Naming conventions:

- `<case>.lit`: one Litex source file per case.
- `<case>_<method>.lean` or `<case>__<method>.lean`: one Lean proof route for
  the same statement. The `_` and `__` separators follow each batch's records.
- `new-round/Repeat.lean`, `new-round/Validate.lean`, `multi-step/Repeat.lean`
  and `multi-step/Validate.lean`: generated timing/validation files, not cases.

Lean timing-case files include `import Mathlib`; timing drivers may also
include `import Lean`. Each can be checked with `lake env lean <file>`.
The timing runner is `../harness/bench.py`.

`lean-proof-pipeline/` needs only `import Lean` and runs directly with Lean
4.31.0. Its output explains proof checking and is excluded from timing statistics.

Historical whole-process records for `quantitative-iteration/` are in the main
README. The original input hashes match the six copies here. Do not combine
those records with checking-path samples that exclude startup/imports.

The shared informal mathematical texts for the three generated batches and
the guarded reciprocal are in
[`cases/informal-baselines.json`](../cases/informal-baselines.json). They are
English retrospective baselines written after the formal sources. The
[de Bruijn counting record](../results/de-bruijn-factors.json) includes source
lengths and hashes; factors are omitted for two sources that differ from their
saved timing-case definitions. See the [measurement method](../README.md#de-bruijn-factor).
