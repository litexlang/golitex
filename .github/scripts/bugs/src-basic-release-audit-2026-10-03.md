# BR002: predeploy Cargo filter can pass with zero executed tests

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

Primary label: `trust` (test-tooling coverage). Repair ownership: local runner/registration repair after checking real collectors; no kernel change.

```python
GATES = (("docs", "run_docs_markdown_files"),
         ("examples", "run_examples_only"),
         ("showcases", "run_showcases"))
```

Executed `cargo test --release --offline run_examples_only`: exit 0, zero tests executed in all targets. The predeploy runner accepts returncode 0 without checking test count. Actual output is retained in `release_basics/proof_journals/zero-collector.log`.

Acceptance: each gate invokes its real collector with a nonzero declared scope; zero selection, missing registrations and timeout fail. Do not rename a filter without proving it collects the intended scope.
