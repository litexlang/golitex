# Function-set composition tests

> **统一收尾入口：** [src收尾总清单.md](../../plan/src收尾总清单.md)（2026-10-04）。活动事项及跨来源去重在总清单维护；本页保留专项代码、决定和历史验收。新增进展应同步对应总清单ID，不能用旧快照覆盖新证据。

This standalone corpus checks function sets, template instantiation, callable
struct fields, function-valued returns and template failure diagnostics.

The current supported regression suite has **85 cases: 58 accepted positives
and 27 correctly rejected negatives**, all matching in strict release mode.
Nine formerly direct-only goals now use the checked explicit proof routes the
user requested. Their original source and the exact field-premise attempt
remain as **10 separate capability observations**. Rejection of a true direct
claim is recorded as an observation, never as a passing mathematical negative.

| Family | Accepted positives | Correctly rejected negatives |
| --- | ---: | ---: |
| Basic function sets | 5 | 3 |
| Templates | 8 | 3 |
| Struct fields | 9 | 4 |
| Higher-order functions | 11 | 7 |
| Explicit typing controls | 14 | 0 |
| Exact function-body evaluation | 2 | 1 |
| Explicit proof routes | 8 | 4 |
| Fixed-signature parse boundaries | 0 | 3 |
| Template diagnostics and obsolete signature | 1 | 2 |

[acceptance.md](acceptance.md) contains the executed source and remaining
boundaries; [todo.md](todo.md) records their disposition. Current receipts:
[cleanup_2026-10-04.json](cleanup_2026-10-04.json),
[capabilities_2026-10-04.json](capabilities_2026-10-04.json),
[cleanup_tests_2026-10-04.json](cleanup_tests_2026-10-04.json) and
[old_fn_set_2026-10-04.json](old_fn_set_2026-10-04.json).

From the repository root:

```sh
python3 examples/test_function_sets/run.py
python3 examples/test_function_sets/run.py --capabilities
python3 examples/test_function_sets/run.py --case H01 --case E01 --case N17 --case N21
python3 examples/test_function_sets/run.py --case P01 --case P02 --case P07 --case P08 --case N25 --case N26
python3 examples/test_objs/run.py --object fn_set
```

The runner builds current release source, inventories all supported and
capability files, runs each selected file with `-strict`, and checks the JSON
envelope, exit status and all setup statements. Timeouts, crashes, unexpected
stderr, invalid protocol and changed source/binary cannot pass as negatives.
N26 also requires the nested template stage and failed membership goal.
`--capabilities` records `matches: null`; its exit status checks completion
without infrastructure failures, not acceptance of the observed true claims.
Default output is `results.json`; use `--report` for another receipt.

The earlier numeric enhancement checks bounded function-body substitution
followed by existing exact arithmetic, preserving signature and domain checks.
This cleanup adds explicit proof fixtures and projects existing template
failure payloads in Normal/Detailed JSON. It does not change verification,
AST, Runtime/Env, search permissions or trust. Successful template output is
unchanged; the old fn-set positive is replaced by a valid fixed-carrier family,
with its invalid original signature retained as N27.

Persistent strict REPL evidence is in
[proof_journals/cleanup_2026-10-04.json](proof_journals/cleanup_2026-10-04.json).
The current CLI lacks `try:`, `-runner`, `-compact` and `-before`; session probes
use discarded `sketch:` frames and clean gates check `success`/`session_error`.
Both raw field-premise orderings are recorded separately. A typed local `&Box`
binding is still required for selected/returned struct field syntax.

Historical receipts remain intact:
[audit_2026-10-04.json](audit_2026-10-04.json) (initial 67 cases),
[numeric_evaluation_2026-10-04.json](numeric_evaluation_2026-10-04.json) (70 cases),
[numeric_evaluation_tests.json](numeric_evaluation_tests.json) (70 Rust tests),
[explicit_proofs_2026-10-04.json](explicit_proofs_2026-10-04.json) (82 cases),
[numeric_evaluation_checkpoint_2026-10-04.json](numeric_evaluation_checkpoint_2026-10-04.json)
and [existing_regressions.json](existing_regressions.json). Their dated
identities describe earlier observations, not current-version assertions.
Earlier source attempts remain in
[proof_journals/2026-10-04.json](proof_journals/2026-10-04.json),
[proof_journals/numeric_evaluation_2026-10-04.json](proof_journals/numeric_evaluation_2026-10-04.json)
and [proof_journals/explicit_bridges_2026-10-04.json](proof_journals/explicit_bridges_2026-10-04.json).

This suite certifies these CLI verification and well-definedness observations.
It does not certify extracted programs, Lean output, performance, all examples
or behavior outside the inventoried fixtures.
