# Obj corpus acceptance

Task: one detailed Litex regression file per Obj variant.

Latest status: the [2026-10-03 recheck](audit_2026-10-03.md) observes 67 remaining
direct rejections, all 99 positive files passing, and all 284 negative fixtures
rejecting. The earlier implementation snapshots below remain historical.

## Tracer: exact division and its WD boundary

The existing division WD example only introduced a value:

```litex
# Existing examples/wd/obj/scalar_div.lit
let q = 1 / 2
```

The dedicated [div.lit](div.lit) now independently verifies exact values, sign, associativity/precedence and symbolic nonzero division:

```litex
6 / 2 = 3
(1 / 2) + (1 / 2) = 1
8 / 2 / 2 = 2
8 / (2 / 2) = 8
```

Executable boundaries also check a zero denominator, an unproved nonzero denominator, a wrong value and a nonnumeric divisor. For example:

```litex
# negative/div__n01.lit: must reject
let x = 1 / 0
```

A complex inverse was originally a separate gap. It is now checked in `div.lit`
case `P08`; the repair journal below preserves its rejected baseline.

## Initial complete-suite verification snapshot

- 99 terminal Obj paths audited against `src/ast/obj.rs`, including all nested interval and number-set alternatives and the helper enums.
- 461 independently scoped positive cases in 99 dedicated files.
- 261 negative fixtures: 254 correctly rejected; 7 incorrect admissions retained as defects.
- 103 direct positive cases retained as unresolved proof/WD boundaries.
- All `.lit` fixtures are inventoried, nonempty and free of trust.
- The intended-behavior gate remains nonzero because the defects and unresolved cases are included.
- The baseline gate passes only if all recorded observations reproduce; no negative/gap is skipped.

```sh
cargo build --release
target/release/litex -f examples/test_objs/div.lit
python3 examples/test_objs/run.py --audit-only
python3 examples/test_objs/test_runner.py
python3 examples/test_objs/run.py --report examples/test_objs/results.json
python3 examples/test_objs/run.py --baseline --report examples/test_objs/baseline.json
```

Baseline snapshot executable: `b128f1c404a38f16c7f4d0ba9ab6394951ba9b600be9c6e9a9de49cdcd940b2a`.

Baseline snapshot source: `4a21ba75a90faf5103376d6fcb69bba9abb9909df83912c3a83966144ff175be`.

The runner built the current source before each final gate. Source and executable remained stable within each gate; the two reports have different snapshot hashes because concurrent source work continued between runs. Every recorded gap has the same observed outcome and phase in both reports. See the reports for each snapshot's exit codes and diagnostics. Broader Rust unit tests, docs, textbook and Lean suites were outside this test-corpus change; no shared semantic contract was changed by this task.

The runner's nine protocol/coverage boundary tests passed, including the control that a failed build must execute no fixture.

## Source updates observed during this task

A concurrent update added nonempty-index requirements. Previously accepted empty-index examples were retired in the positive files and replaced with executable `N_EMPTY` negatives; their original journal observations remain historical, not current acceptance evidence. A transient compile failure in that work was resolved before final verification.

The same unchanged callable-template alias that initially failed now passes after that concurrent source update, so it was promoted to `instantiated_template_obj.lit` case `P04`:

```litex
template<S set>:
    have fn identity(x S) S = x
let f = \identity<R>
f(2) = 2
```

This task did not implement the engine repair; it captured the successful behavior in the corpus.

Temporary staging scripts and probes were removed after durable journals, reports and issue records were written. Earlier unrelated workspace edits were preserved.

## Follow-up diagnosis (2026-10-02)

The written inventory now contains 262 negative fixtures and 111 recorded gaps. The new negative [number__n03.lit](negative/number__n03.lit) must reject:

```litex
2.400 != 2.4
```

The release verifier instead accepted it through `Closed decimal inequality`. See [diagnosis_2026-10-02.md](diagnosis_2026-10-02.md) for the normalization cause, the two complex-inverse barriers and the proposed finite-sum reduction. The follow-up ran a focused Number gate; it did not rerun the complete corpus or change kernel semantics. `number_diagnosis_baseline.json` and `number_diagnosis_results.json` record that focused snapshot; the earlier `baseline.json` and `results.json` describe the initial full gate and earlier inventory.

## Approved numeric and aggregate implementation (2026-10-02)

The four approved stages are implemented. These direct assertions now verify:

```litex
2.400 = 2.4
i != 0
1 / i = -i
sum(1, 3, fn(x Z) Z {x}) = 6
product(1, 3, fn(x Z) Z {x}) = 6
```

The false decimal inequality, `i = 0`, `1 / i = -1`, zero denominators,
out-of-domain callable applications and incorrect aggregate results remain
rejections. Exact rational inequality also supports displayed fractional index
sets without accepting equal fractions as distinct elements.

Finite evaluation covers anonymous/named functions and aliases, checked algorithm
equations, mixed nested sums/products, exact fractions, displayed sets and known
enumerations. Symbolic evidence covers constant, pointwise, sum linearity/scalar,
adjacent partition, integer shift, disjoint finite union and range/set bridge
rules. Unknown endpoints use those rules with checked premises, rather than
inventing an enumeration. Detailed output retains application WD, function
equations, each term and running folds. Normal English/Chinese output shows the
evaluated object and the budget/overflow cause.

The selected seven-object intended gate checks 78 positive cases and 46 rejection
fixtures with no failures; see [the focused report](numeric_aggregate_focused_results.json).
All 99 owning positive files pass the complete gate. The written inventory is
524 positives, 284 rejection fixtures and 72 surviving gap fixtures: 71 valid
direct assertions still reject, and one invalid finite-set reduction still
accepts. The complete intended gate therefore exits nonzero; see
[the complete report](numeric_aggregate_results.json) and [the issue list](todo.md).
The 15 numeric/aggregate repairs preserve their original failure sources in
[the promotion journal](proof_journals/numeric_aggregate_promotions_2026-10-02.json).
24 other unchanged fixtures recovered during concurrent engine work; this task
records their promotion without claiming those engine changes.

The final feature, output, documentation and Rust evidence is retained in
[the verification journal](proof_journals/numeric_aggregate_gate_2026-10-02.json).
The 13 Rust filters collected and passed 246 tests; 27 feature/doc/output probes and both shift-domain controls also passed.
Final gates build an immutable copy of the workspace's Rust/corpus inputs,
because other tasks continued editing the shared checkout. Source and binary
hashes identify that checked snapshot; they do not certify subsequent unrelated
edits. Failed/inconsistent shared-checkout builds executed no acceptance fixtures.
AST/fixture auditing and all nine runner protocol tests pass, including the
failed-build control. Earlier `baseline.json`, `results.json` and diagnosis
reports are historical snapshots.

Scope and limits:

- This repair changes shared exact-number and aggregate WD/evidence entrances,
  with focused tests for their consumers. It adds no Obj/Stmt/Fact or Env/Runtime
  shape changes. `eval` displays results and stores no mathematical equation;
  direct equalities publish their checked facts.
- Nested calculation shares 1024 terms, depth is bounded and integer endpoint
  arithmetic is checked. Resource exhaustion is a failure, not a numeric result.
- Reversed range sums/products still reject. Empty finite-set sum/product use
  0/1. Infinite aggregates and unspecified set enumerations are not numeric eval.
- A symbolic shift can still require an explicit target-interval hypothesis,
  such as `3 <= n + 2`; the unproved legality obligation remains in the todo.
- ABI 3 invalidates old products after the numeric/WD correctness correction;
  subsequent unrelated interface changes raised the current revision to ABI 4.
  Older imported products rebuild through the existing cold fallback. Cache
  rejection and cold-rebuild/warm-hit tests cover this compatibility change.
- No claim of Lean export or a globally defect-free kernel is made by these gates.

Reproduce from the repository root:

```sh
python3 examples/test_objs/run.py --object number --object imaginary_unit --object div --object sum --object product --object sum_of_finite_set --object product_of_finite_set
python3 examples/test_objs/run.py --audit-only
python3 examples/test_objs/test_runner.py
python3 examples/test_objs/run.py --report examples/test_objs/numeric_aggregate_results.json
```

## Diagnostic recheck (2026-10-03)

The unchanged invalid unordered subtraction fold now rejects during its `let`
WD check:

```litex
let r = finite_set_reduce({1, 2}, fn(x Z) Z {x}, fn(a, b Z) Z {a - b}, 0)
```

Four addition-fold gaps also meet their intended results. The current-source
release build succeeds and remains stable through the full gate. All 99
positive files (524 written cases) pass; all 284 negatives reject. Of the 72
historically recorded gap fixtures, five recovered and 67 valid direct cases
still reject. No operational failure or incorrect negative admission is
observed in this corpus. The intended gate correctly exits 1.

The AST/fixture audit and nine runner protocol tests pass. This round retains
24 concrete probes, distinguishing successful explicit proof routes from
unchanged direct-assertion failures. It changes records only, preserves every
fixture and historical report, and closes the five recovered todo entries
after saving [solution evidence](experience/problem_notes/obj_recheck_2026-10-03.md).
No implementation change is attributed to this diagnostic task.

See [the audit](audit_2026-10-03.md), [full process report](audit_2026-10-03_results.json)
and [source/output journal](proof_journals/obj_audit_2026-10-03.json). Their source
and binary hashes identify the checked snapshot. Subsequent concurrent
ByCases/ByContra source edits are outside this evidence; the last five probes
used the retained executable from the completed stable audit.

```sh
python3 examples/test_objs/run.py --audit-only
python3 examples/test_objs/test_runner.py
python3 examples/test_objs/run.py --report examples/test_objs/audit_2026-10-03_results.json
```

Full Rust, Lean, textbook and release gates were outside this record-only scan.
The finite corpus does not prove a globally defect-free kernel.

## F authoring repairs (2026-10-03)

The direct tracer `union({1}, {2}) = {1, 2}` rejects at proof search;
`by extension union({1}, {2}) = {1, 2}` checks the same equality. It is now
P01 in [union.lit](union.lit), rather than a registered unresolved gap.

This round changes `.lit` proofs and records only. It promotes 23 checked Obj
proof/fixture migrations and four already recovered addition folds. The invalid
unordered subtraction case remains a negative fixture. The live manifest has
551 positive cases and 44 residual positive gaps; 284 negatives are retained.
B10 now uses an explicit named theorem in ordinary mode, retaining its four
opaque trust commands; it is not a strict mathematical proof.

See [the recipes and remaining boundaries](experience/problem_notes/f_authoring_repairs_2026-10-03.md)
and [the complete journal](proof_journals/f_authoring_repairs_2026-10-03.json).
The initial successful release was frozen before proof iteration. A later
current-source collector build failed during concurrent `VerifyState` edits;
that invocation executed no acceptance fixtures. Frozen-release gates and
any subsequent build checks are recorded with their actual binary identities.
Full Rust, Lean, textbook and publication gates are outside these source-proof
changes. No AST, runtime or search-budget change was made by this task.

Final frozen-release gate: all 99 positive files (551 cases) pass under strict
mode; all 284 negatives reject; all 44 residual direct gaps reject, so the
intended full corpus remains non-green. All 81 independent strict frame replays
match the persistent-session outcomes. B10 succeeds in ordinary mode only.
Inventory audit and nine runner protocol tests pass; this task's diff check
passes. The final current-source build retry also fails (exit 101), with duplicate
`VerifyState` definitions and mismatched fields. Both failed current builds ran
no acceptance fixtures. These records certify the preserved release, not the
concurrent unfinished kernel state.
