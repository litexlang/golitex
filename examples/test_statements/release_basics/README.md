# Basic src release contracts

Task: execute the maintainer's 2026-10-03 request for a detailed basic semantic
and functionality audit. Design: `plan/迁移的plan/src上线前基础语义与功能测试.md`.

This corpus covers 40 named contracts with independent positive and negative
Litex fixtures, exact evaluation values, persistent Runtime/REPL controls,
real import/cache projects, public entry points and repeated fresh processes.
False conclusions, ill-defined expressions, unsupported interfaces and parser
errors have separate expectations. Mathematical fixtures run in strict mode.

Run from the repository root after building the current release source:

```sh
cargo build --release
python3 examples/test_statements/release_basics/run.py \
  --binary target/release/litex \
  --manifest examples/test_statements/release_basics/cases.json \
  --workdir tmp/2026-10-03/src-basic-release-audit/rerun \
  --report tmp/2026-10-03/src-basic-release-audit/rerun.json
```

The runner rejects missing contract collection, mismatched per-statement
results, incorrect eval values, timeout, abnormal process exit, invalid JSON
and executable drift. Module fixture files are disposable, task-owned files
under the supplied work directory; the module controls recreate only their own
`modules/` child to guarantee a cold initial run. Supply a dedicated work area.

This is a separate explicitly invoked gate. The existing root Stmt collector
still inventories its 50 primary `.lit` files; it does not implicitly discover
this nested corpus. A green observed-baseline runner or zero-selected Cargo
filter does not establish these contracts.

See the dated audit, coverage receipt and proof journals here for executed
results. They identify the exact source/binary snapshot. Failure counts are
test observations, not counts of independent kernel bugs. No kernel or AST
repair is performed by this audit.
