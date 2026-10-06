# Complete ordinary theorem-release spelling migration

> Historical audit: these code fences preserve dated verifier observations,
> including rejected inputs and excerpts that depend on their original context.
> They are evidence, not current standalone tutorial examples. The maintained
> executable language examples are in the Manual, README, and examples corpus.

Recorded at 2026-10-05T21:29:43.967199+08:00. This completes the remaining current-authoring `.lit`
spelling batch after the earlier documentation/examples/geometry migration.
Only accepted bare theorem-call command tokens changed from `by` to `release`;
selected calls, mathematical statements, arguments, source lines, proof order,
trust and interfaces are preserved. Parser/runtime/kernel/configuration code
was not changed by this task.

## Actual before/current tracer and runtime outcome

The actual source is
[`新IMO/problem_5/Solution-1/solution.lit`](../../scripts/LitexGeo-AutoBuild/shenjiachen/新IMO/problem_5/Solution-1/solution.lit),
line 73. This excerpt depends on the declarations in that file.

<!-- litex:skip-test -->
```litex
# Before:
# by thm isosceles_euler_square(a, h, s, r, rho, d)

# Current:
release thm isosceles_euler_square(a, h, s, r, rho, d)
```

The same frozen current release executable verified the entire actual file
before and after: five successful declarations, exit 0, `success: true`,
`session_error: null`. Before: 112.093 seconds; after:
111.586 seconds. Its other bare call to
`nonnegative_square_root(d, r * (r - 2 * rho))` was also migrated.

## Completed scope

| Workspace | Files | Replacements |
| --- | ---: | ---: |
| scripts/Analysis | 69 | 6,366 |
| scripts/Analysis2 | 11 | 188 |
| scripts/Concrete-Mathematics-A-Foundation-For-Computer-Science | 5 | 107 |
| scripts/LitexGeo-AutoBuild | 6 | 102 |
| scripts/MATH-500-litex | 7 | 18 |
| scripts/high_school_book | 23 | 100 |
| scripts/linear_algebra_done_right | 172 | 4,086 |
| scripts/linear_algebra_done_right2 | 4 | 126 |
| scripts/litex-minif2f | 20 | 71 |
| scripts/math_concepts_in_litex_upstream | 3 | 21 |
| scripts/mathematics_in_litex | 32 | 1,836 |
| scripts/number_theory_for_beginners | 3 | 8 |
| scripts/新geo的imo的草稿 | 3 | 53 |
| Total | 358 | 13,082 |

Seven canonical Analysis chapter/appendix files account for 859 replacements;
other rows include working `.draft`/`.drafts`, experiments, backlog and probes.
Every changed source was compared byte-for-byte with its immutable before
snapshot. All other bytes and physical source lines are unchanged. A full
rescan found **zero ordinary bare aliases in current authoring scope**.
All 1,065 selected `by thm ... => fact` calls are preserved, as is the
intentional colon-body rejection fixture.

The automatic-builder prompt source
[`litex_short_guide.md`](../../scripts/LitexGeo-AutoBuild/litex_auto_build_system/litex_short_guide.md)
is read by `run_litex_theorems.py:1492`. Its four bare code heads and 14
ordinary prose/code mentions now use `release thm`; it explicitly keeps
`by thm ... => fact` for selection and bare `by thm` as compatibility syntax.
The actual two-theorem addition-cancellation documentation example passed
before and after on the same executable.

A concurrently authored `新IMO/problem_4/solution.lit` appeared during the
final rescan. Its latest 41 bare calls were snapshotted, checked with the
native tokenizer/parser, and migrated without changing its proof content;
its three selected calls were added to the preserved-call inventory.

## Native equivalence and execution coverage

The frozen executable is Litex 0.9.200-beta, SHA256
`280a87ff7afb6452ef50ae0a3829568b6c0c9da85d90a0740817659a5b473dcc`. Its matching frozen library SHA256 is
`81af272ba0099be4b7ce78f2cbc338dc9bd69d432eacce62930b611d3145d8bb`. The executable/library hashes
remained unchanged throughout this task, despite other concurrent source edits.

Using the native library, all 358 complete files tokenize identically after
normalizing only the 13,082 identified bare command tokens. TokenBlock headers,
bodies, arguments, source paths and physical line numbers are otherwise equal.
The 39 files that parse in an isolated parse-only Runtime have identical full
parsed AST Debug representations before/after. The other 319 produce identical isolated parse results at
their existing boundary. Parse-only checks do not execute preceding declarations
or load configured module prefixes; these results are not 319 runtime-failure
claims. Proposed-after snapshots were checked first, then every actual source
was verified byte-identical to its checked proposal.

All 41 real before/after `-strict -f` scenarios have matching exit status,
top-level success/error, statement count, successful/failed statement positions
and first failure statement. Three positive scenarios pass: the actual IMO
file above, the selected-theorem fixture and the changed generator-guide
example. The two intentional rejection controls retain rejection. The other
36 scenarios have existing failures, with identical post-migration boundaries.
There were no timeouts or inconclusive results. This does **not** claim every
old mathematical proof in the repository runs on the current kernel.

## Existing compatibility boundaries, unchanged by this batch

The actual Analysis tracer is
[`chapter03-set-theory.lit`](../../scripts/Analysis/textbook/chapter03-set-theory.lit)
at line 852:

<!-- litex:skip-test -->
```litex
# Before:
# by thm set_builder_member(2, {n N: n < 4})
release thm set_builder_member(2, {n N: n < 4})
```

Both full registered runs stop before that code at the same configuration
launch error. Its current configuration contains:

```text
[hierarchy]
module
```

Current CLI outcome, both before and after:
`launch_error: litex.config:1: litex.config does not use [hierarchy] or [module]`
(exit 2). No configuration was rewritten to obscure this existing boundary.

A concrete miniF2F example,
[`induction_sumkexp3eqsumksq.lit`](../../scripts/litex-minif2f/finished/induction_sumkexp3eqsumksq.lit),
line 8, still contains the unchanged legacy dependency statement:

<!-- litex:skip-test -->
```litex
import "../cite" as MiniF2FCite
```

Both runs reject it with
`` `import` is not a Litex statement; declare dependencies in litex.config ``.
Other pre-existing proof/definition failures are listed individually in the
machine receipt and captured outputs. Repairing those compatibility/proof
issues is separate from this equivalent-spelling batch; no trust or weaker
statement was introduced to make them appear successful.

## Preserved evidence and exact artifacts

82 files retain 6,775 bare occurrences as historical or compatibility evidence:
previous-publication snapshots, old textbook versions, legacy quarantine,
explicit before-state sources, backups, bundled old skill-reference examples,
experience repros and captured `run_YYYYMMDD_HHMMSS` build outputs. Task/audit
copies under `tmp/` and workspace-local `private/` are outside current-source
migration scope. Commented examples and factual journals/receipts also retain
their original text. These are explicit preserved exceptions, not unfinished
current-authoring batches. Bare parser compatibility remains supported.

Detailed hashes, per-line locations, preserved paths and execution comparisons
are in [the machine receipt](by-thm-release-completion-2026-10-05.json).
Immutable source snapshots, frozen executable/library, native comparison probe
and raw results remain in the allocated task area:
`tmp/2026-10-05/by-thm-release-completion/`.

Exact positive source gate:

```text
tmp/2026-10-05/by-thm-release-completion/litex-current -strict -f scripts/LitexGeo-AutoBuild/shenjiachen/新IMO/problem_5/Solution-1/solution.lit
```

This is L1 equivalent-source maintenance with no shared contract change. No
full Rust/kernel/Lean/release suite or exhaustive proof rerun was needed for
this spelling-only acceptance. The earlier complete 227-declaration geometry
run remains documented separately under its source/binary hashes.
