# Function-set composition audit

Task: test function sets, template instantiation, callable struct fields and
function-valued returns, requested on 2026-10-04. This is a standalone test
corpus, not an exported mathematical module.

The initial 67-case audit accepted 27 of 47 positive goals and rejected all
20 negative boundaries. The subsequent authorized function-body enhancement
fixes **11 previously rejected positives** and adds two exact numeric tracers
and one precision boundary. The user's subsequent explicit-proof contract
adds eight checked proof routes and four negative controls. The current
82-case corpus accepts **48 of 57 positives** and rejects **all 25 negatives**.
Nine original direct probes still reject, and each has a checked explicit
route. They measure direct verification capability; their rejection does not
establish nine kernel bugs. The full corpus retains their `expect: accept`
and returns exit 1.

| Family | Positive goals | Accepted | Must-reject goals | Correctly rejected |
| --- | ---: | ---: | ---: | ---: |
| Basic function sets | 5 | 5 | 3 | 3 |
| Templates | 8 | 6 | 3 | 3 |
| Struct fields | 9 | 6 | 4 | 4 |
| Higher-order functions | 11 | 10 | 7 | 7 |
| Explicit proof and typing controls | 14 | 11 | 0 | 0 |
| Exact function-body evaluation | 2 | 2 | 1 | 1 |
| Explicit routes under the user's proof contract | 8 | 8 | 4 | 4 |
| Fixed-signature parse boundaries | 0 | 0 | 3 | 3 |

See [acceptance.md](acceptance.md) for the current direct-value capability, historical proof routes and
remaining limitations, [todo.md](todo.md) for open investigation items, and
[audit_2026-10-04.json](audit_2026-10-04.json) for the original dated source/binary/fixture
receipts. [numeric_evaluation_2026-10-04.json](numeric_evaluation_2026-10-04.json)
records the current enhancement; [numeric_evaluation_tests.json](numeric_evaluation_tests.json)
records its 70 passing focused Rust tests. [explicit_proofs_2026-10-04.json](explicit_proofs_2026-10-04.json)
records the current explicit-proof audit without further kernel changes.
[numeric_evaluation_checkpoint_2026-10-04.json](numeric_evaluation_checkpoint_2026-10-04.json)
retains the earlier accepted release while the final gate incorporates parallel source updates. [existing_regressions.json](existing_regressions.json) records 23
passing focused Rust tests and four existing CLI tracers: three pass and the
older object-corpus fixture rejects its obsolete dependent return carrier.

From the repository root:

```sh
python3 examples/test_function_sets/run.py
python3 examples/test_function_sets/run.py --case H01 --case H02 --case H07 --case E01 --case N17 --case N21
python3 examples/test_function_sets/run.py --case D12 --case D13 --case D14
python3 examples/test_function_sets/run.py --case P01 --case P02 --case P03 --case P04 --case P05 --case P06 --case P07 --case P08 --case N22 --case N23 --case N24 --case N25
```

The runner builds current release source, checks fixture inventory, runs each
file with `-strict`, and checks the production JSON envelope together with the
exit status and all setup statements. A timeout, crash, unexpected stderr,
invalid protocol or changed source/binary cannot pass as a negative test.
Known positive failures retain `expect: accept`; they are never counted as
successful rejections. Default output is `results.json`; use `--report` to
choose another receipt. The dated receipts are retained observations, not permanent assertions about
later versions.

The enhancement uses bounded, checked body substitution in the function
object-definition equality route, followed by existing exact arithmetic.
It preserves signature/domain checks and the shared single-step helper used
by restricted builtin and aggregate premises. Detailed output retains each
selected body, application WD, body-specific WD and continuation. No AST,
Runtime/Env contracts, global search permissions, or trust were changed.

Every fixture is independent. The initial source-order probes used discarded
`sketch:` frames in a strict persistent REPL; their materially distinct source
attempts are in [proof_journals/2026-10-04.json](proof_journals/2026-10-04.json).
The enhancement's before/after session evidence is in
[proof_journals/numeric_evaluation_2026-10-04.json](proof_journals/numeric_evaluation_2026-10-04.json).
The explicit-proof attempts, including the user's exact struct chain and its
WD failure before field evaluation, are in
[proof_journals/explicit_bridges_2026-10-04.json](proof_journals/explicit_bridges_2026-10-04.json).
The current CLI has no `try:`, `-runner`, `-compact` or `-before`, so clean gates
use top-level `success` and `session_error`. Final clean gates rechecked all
fixtures after concurrent source changes invalidated one intermediate build.

This audit covers verification and well-definedness through the Litex CLI. It
does not certify extracted programs, Lean output, performance, all examples,
or the absence of bugs outside these fixtures.
