# Function-set composition audit

Task: test function sets, template instantiation, callable struct fields and
function-valued returns, requested on 2026-10-04. This is a standalone test
corpus, not an exported mathematical module. No kernel code or trust was added.

The current release audit contains **67 independent fixtures**: 47 positive
goals and 20 must-reject boundaries. **27 positives pass; 20 positives remain
rejected; all 20 negatives reject at their expected phase after successful
setup.** Thus 47 expectations match and the complete suite returns exit 1.
The 20 rejected positives are not 20 independently diagnosed bugs: several
exercise direct assertions for which an explicit checked proof route works.

| Family | Positive goals | Accepted | Must-reject goals | Correctly rejected |
| --- | ---: | ---: | ---: | ---: |
| Basic function sets | 5 | 5 | 3 | 3 |
| Templates | 8 | 4 | 3 | 3 |
| Struct fields | 9 | 6 | 4 | 4 |
| Higher-order functions | 11 | 1 | 7 | 7 |
| Explicit proof and typing controls | 14 | 11 | 0 | 0 |
| Fixed-signature parse boundaries | 0 | 0 | 3 | 3 |

See [acceptance.md](acceptance.md) for concrete passing proof routes and
limitations, [todo.md](todo.md) for open investigation items, and
[audit_2026-10-04.json](audit_2026-10-04.json) for the dated source/binary/fixture
receipts. [existing_regressions.json](existing_regressions.json) records 23
passing focused Rust tests and four existing CLI tracers: three pass and the
older object-corpus fixture rejects its obsolete dependent return carrier.

From the repository root:

```sh
python3 examples/test_function_sets/run.py
python3 examples/test_function_sets/run.py --case H01 --case H02 --case D02
python3 examples/test_function_sets/run.py --case D12 --case D13 --case D14
```

The runner builds current release source, checks fixture inventory, runs each
file with `-strict`, and checks the production JSON envelope together with the
exit status and all setup statements. A timeout, crash, unexpected stderr,
invalid protocol or changed source/binary cannot pass as a negative test.
Known positive failures retain `expect: accept`; they are never counted as
successful rejections. Default output is `results.json`; use `--report` to
choose another receipt. The dated audit is the retained observation, not a
permanent assertion about later versions.

Every fixture is independent. The initial source-order probes used discarded
`sketch:` frames in a strict persistent REPL; their materially distinct source
attempts are in [proof_journals/2026-10-04.json](proof_journals/2026-10-04.json).
The current CLI has no `try:`, `-runner`, `-compact` or `-before`, so clean gates
use top-level `success` and `session_error`. Final clean gates rechecked all
fixtures after concurrent source changes invalidated one intermediate build.

This audit covers verification and well-definedness through the Litex CLI. It
does not certify extracted programs, Lean output, performance, all examples,
or the absence of bugs outside these fixtures.
