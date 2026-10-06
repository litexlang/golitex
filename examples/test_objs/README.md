# Obj regression corpus

The 2026-10-06 tuple/cart source migration uses ordinary calls such as
`pair(1)`, checked coordinate types and explicit intermediate equalities.
The tuple, cart, identifier, list-set and struct-field files selected in the
[source-only migration journal](../../plan/迁移的plan/proof_journals/tuple-cart-source-only-migration-2026-10-06.json)
have fresh strict file receipts. Nested values are selected into a checked
local name when the direct chained-call form lacks usable evidence.
The old tuple/cart dimension, shape and construction-projection interfaces
are retired. Their dedicated historical fixtures await collector retirement;
they are not current must-pass language examples. This source-only batch does
not change Rust, rebuild the verifier or certify the entire Obj corpus.

The [2026-10-05 cross-Obj relation audit](obj_relations_audit_2026-10-05.md)
checks 81 representative interactions and partitions the recorded 99-object
inventory. It separates direct support, checked author routes, restricted
domains and remaining interface candidates. The [38 explicit author routes](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit)
pass a strict standalone gate; this focused result does not certify every
owning Obj file, including the concurrently changed `cart_dim` boundary.

The subsequent [common relation completion](../proof_nodes/experience/problem_notes/common-obj-relations-2026-10-05.md)
supplies the selected gcd/lcm, factorial/product, sine-interval and general
positive logarithm-base interfaces, with dedicated examples and focused boundary
checks. The remaining LEG35/36 trigonometric cases keep their existing owners.

> **统一收尾入口：** [src收尾总清单.md](../../plan/src收尾总清单.md)（2026-10-04）。活动事项及跨来源去重在总清单维护；本页保留专项代码、决定和历史验收。新增进展应同步对应总清单ID，不能用旧快照覆盖新证据。

原审计的32个问题主题按原编号列在[逐项清理计划](../../plan/src收尾总清单.md#obj-original-32)：第1项的显式Litex证明与第3项的 eval 结果存储已完成，第2项已撤回。关闭项从[活动纠错记录](remaining_issues_2026-10-04.md)删除；[eval 解法及验收](experience/problem_notes/eval_store_result_2026-10-04.md)保留经验与回执，其余按原编号对应总清单。

[符号聚合三项的最新复核](experience/problem_notes/symbolic_aggregate_status_2026-10-04.md)：原十个短式现有 7 个直接通过，3 个已有显式作者证明；五个相关完整文件通过。第4–6项已从活动纠错段落移除，短搜索边界和原始回执保留。

This directory tests the terminal variants reachable from `Obj` in
`src/ast/obj.rs`. Each variant has a dedicated, nonempty positive `.lit` file.
Function-head variants and the `FnSetSpace` helper enum are audited as well.
This is an object corpus; statement and fact inventories remain in the existing
`stmt_nodes` and `proof_nodes` suites.

The cases cover exact numeric values, carriers, precedence, signs, zero,
endpoints, empty containers where legal, nested objects, binders, function
arity/domain/codomain, struct fields, and identifier ownership. Most positive
cases use independent `sketch:` scopes, whose facts and definitions do not
escape to later cases. Rejections and unresolved positive cases are standalone
fixtures. No test uses `trust` to manufacture success.

The approved numeric and aggregate repairs add exact decimal normalization,
imaginary nonzero and guarded division, bounded nested sum/product calculation
and symbolic identities. The [2026-10-03 audit](audit_2026-10-03.md) is a retained
historical snapshot. The subsequent [F authoring repairs](experience/problem_notes/f_authoring_repairs_2026-10-03.md)
promote 23 explicit checked proofs and four recovered folds, leaving 44 gaps and 551 positive cases at that point. The [exact numeric,
periodic trig and modulus repair](experience/problem_notes/exact_numeric_periodic_modulus_2026-10-03.md)
closes 14 more gaps and adds 21 positive and five negative cases. That round left **586 positive cases, 289 negatives and 30 remaining gaps**. Source and binary identities,
gates and any concurrent-build limitations are recorded separately in
[acceptance](acceptance.md) and the authoring journal. No test adds trust.

The [remaining elementary follow-up](experience/problem_notes/remaining_elementary_gaps_2026-10-03.md)
closes the eight finite-rational-extremum, quarter-angle-inverse and log goals
left after the fourteen numeric/periodic/modulus closures. At that checkpoint the manifest
contained **594 positive cases, 289 negatives and 22 remaining gaps**. Inverse
and log cases retain their checked intermediate proofs and principal ranges.


The [closed elementary calculation follow-up](experience/problem_notes/closed_exact_elementary_calculation_2026-10-03.md) adds 33 positive and six negative cases. That round left **627 positive cases, 295 negatives and 22 remaining gaps**. Four dedicated tracers and paired negatives cover calculation and exact display evaluation; a focused result is not a new complete-suite certificate.

The latest full scan also finds [39 owning-file regressions](current_source_regressions_2026-10-03.md)
after concurrent kernel changes: 37 rejections and two protocol failures.
They are separate from the direct-gap inventory. Focused feature success does
not make this complete corpus green; consult the dated source/binary receipts.

The [explicit set-proof follow-up](experience/problem_notes/remaining_set_proof_repairs_2026-10-03.md) closes 17 more gaps with contra, extension, carrier proofs and definition release. That round left **644 positive cases, 295 negatives and 5 remaining gaps**; its strict focused gate covers 11 owning files and 28 rejection fixtures.

The [five-set follow-up](experience/problem_notes/five_set_gap_followup_2026-10-03.md) closes the last five recorded gaps. The current audited inventory has **665 positive cases, 309 negatives and 0 recorded gaps**. Concurrent unrelated additions contribute to these totals; this round closes five cases and adds five negatives. Its focused gates do not certify the full corpus.

## Run

The [exact rational-power addition](experience/problem_notes/exact_rational_powers_2026-10-03.md)
adds 16 positive and nine negative Pow cases. Its 23 selected Rust tests and
38 strict CLI checks pass, including exact eval values and retained integer
domains. Three previously recorded mixed-module test expectations still fail;
their before/after calculation receipts are retained separately. Consult
[coverage.md](coverage.md) for current counts; this is not a full-corpus gate.

From the repository root:

```sh
cargo build --release
python3 examples/test_objs/run.py
```

The runner first builds the current release source and stops if compilation
fails, so an older executable cannot masquerade as current verification.
The default command checks intended behavior, including recorded gaps. It
returns nonzero while any legitimate positive still fails, or any forbidden
input still succeeds. It also rejects timeouts, crashes, invalid JSON,
exit/JSON disagreement, incomplete fixture inventories, and uncovered AST
variants. A known defect is never converted into a passing semantic test.

To reproduce the complete observed baseline, including known defects:

```sh
python3 examples/test_objs/run.py --baseline --report examples/test_objs/baseline.json
```

Baseline success means the recorded observations reproduced. It does not mean
the known defects are fixed. A fixed gap makes the baseline differ; promote its
successful regression or rejection, update the manifest and close its todo.

Focused commands:

```sh
python3 examples/test_objs/run.py --object div
python3 examples/test_objs/run.py --object anonymous_fn --object finite_set_reduce
python3 examples/test_objs/run.py --audit-only
python3 examples/test_objs/test_runner.py
target/release/litex -f examples/test_objs/div.lit
```

Every process is checked using the current CLI's top-level `success` field and
its exit status. Source and executable hashes are recorded in structured
reports; a source/executable change during a gate invalidates it. Build before
running after source changes. This checkout does not support the older workflow
flags `-compact`, `-runner`, `-before` or the `try:` statement. The implementation
journals record ordinary persistent sessions and final clean-file gates instead.

## Layout and evidence

- `*.lit`: independently scoped positive cases, with stable `Pxx` case IDs.
- `identifier_with_*/main.lit`: qualified-name cases with minimal projects
  needed to exercise real export and import ownership.
- `negative/`: individually executable must-reject cases. Some currently
  expose defects; the manifest and todo identify those explicitly.
- `gaps/`: remaining direct positive reproductions. Solved sources are
  archived in proof journals and promoted to their owning positive files.
- `fixtures/`: small maintained library for qualified-identifier tests.
- `coverage.json`: AST path, file, case and observed-gap inventory.
- `baseline.json`, `results.json`: historical complete-suite process observations
  for the initial inventory; consult their hashes and status.
- `number_diagnosis_*.json`: focused follow-up snapshots for the added Number
  inequality regression.
- [diagnosis_2026-10-02.md](diagnosis_2026-10-02.md): checked causes of the
  decimal, complex-inverse and finite-sum examples selected by the user.
- `proof_journals/`: accepted source and materially distinct failed attempts.
- [coverage.md](coverage.md): readable per-object inventory and case counts.
- [audit_2026-10-03.md](audit_2026-10-03.md): preceding scan counts, concrete diagnoses
  and checked explicit proof routes; its journal retains all 24 follow-up probes.
- [todo.md](todo.md): concrete reproductions, exact diagnostics, intended
  outcomes and next actions for surviving issues.
- [acceptance.md](acceptance.md): tracer, selected gates and verification limits.

Do not recursively treat every `.lit` here as a must-pass example: the negative
and gap fixtures deliberately exercise the rejected or defective boundaries.
Use `run.py` to select and interpret them.

## Current language boundaries

These cases follow the implementation's contracts, rather than adding external
mathematical axioms. `N` contains zero. `quot(a, d)` requires `d` in `N+`.
`gcd(a, b)` excludes `(0, 0)`. Displayed list-set entries must be provably
pairwise distinct. Real `abs` is separate from complex `C_abs`. Tuple and
Cartesian-product indices and finite-sequence function domains are one-based.
Integer ranges and real intervals have different endpoint rules.
Range `sum`/`product` require a nonempty range; `reduce` permits an empty range.
Indexed union/intersection/product currently require a nonempty index carrier.
Free-form nested bracket sequences and explicit `&Struct{value}.field` selection
are outside the current syntax.

A rejected mathematically correct direct assertion can be a missing proof route
or an authoring limitation. The todo distinguishes those observations from
confirmed violations of well-definedness contracts. This finite regression
corpus cannot prove the absence of all object bugs.


P200 in `floor`, `ceil`, `tan`, `cot`, `gcd`, `finite_set_max` and
`finite_set_min` covers their defining bounds, guarded quotients, Euclidean
recursion and member bounds. Each case keeps its discarded sketch scope.
The [definition-rule acceptance record](../proof_nodes/experience/problem_notes/obj-definition-builtin-rules-2026-10-05.md)
contains the former failures and nearest rejected domains; the corresponding
`coverage.json` entries include P200.
