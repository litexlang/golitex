# Function-set composition tests

This corpus checks function sets, template instantiation, callable struct
fields, function-valued returns and failure diagnostics. `manifest.json`
separates expected successes, expected rejections and capability observations.

An unsupported direct assertion is recorded as a capability observation,
not as proof that the asserted mathematical statement is false. The runner
checks source and binary identities and records results for the selected files.

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

The current CLI lacks `try:`, `-runner`, `-compact` and `-before`; session probes
use discarded `sketch:` frames and clean gates check `run_result`,
`session_terminated`, and `termination`. A typed local `&Box`
binding is still required for selected/returned struct field syntax.
