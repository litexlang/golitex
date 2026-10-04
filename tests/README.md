# Repository test architecture

All Rust test bodies live under `tests/`. Production files in `src/` contain
only small `#[cfg(test)] #[path = ...] mod ...;` loaders and, where unavoidable,
narrow test-only access seams.

| Directory | Responsibility | How it runs |
| --- | --- | --- |
| `unit/<subsystem>/<responsibility>/` | White-box tests owned by one source responsibility. The subsystem mirrors `src/`; the final directory says what is tested instead of repeating its parent name. | Loaded privately by the owning source module or binary entry under `cfg(test)`. |
| `unit/kernel_contracts/` | Cross-cutting white-box runtime, verifier, dataset-runner, and compiler contracts. | Loaded privately from `src/lib.rs` or the compiler owner. |
| `integration/` | Black-box public API, CLI, output, publication, and repository-boundary tests. | Registered explicitly as Cargo `[[test]]` targets. |
| `tooling/` | Tests for repository scripts and deployment tooling. | Run by the tool-specific Python gate. |

The current Cargo targets run Rust unit tests and the Stmt fixture inventory
integration test. The old `run_examples`, `run_examples_only`,
`run_docs_markdown_files`, and `run_showcases` collectors exist only in the
memorial source; their Cargo filters currently select zero tests. The predeploy
script rejects that empty selection. Collector migration is tracked as REL02
in `plan/src收尾总清单.md`.

## Examples and boundaries

| Command | Actual coverage example |
| --- | --- |
| `python3 examples/test_statements/run.py --binary target/release/litex --require-no-gaps` | Runs the current Stmt manifest, including declared positive and negative cases. |
| `python3 tests/tooling/run_docs_markdown_files.py` | Runs root `README.md` plus `docs/**/*.md` Litex fences via `target/release/litex`. |
| `cargo test --release runtime_contract_builtin -- --nocapture` | Runs the checked-`1 = 1` runtime smoke test. |
| `cargo test --release --all-targets --no-fail-fast` | Runs all registered Rust targets; it does not replace the missing full corpus collectors. |
| A test name containing `run_all` | Does not imply compiler, Lean, textbook, or packaging coverage unless that command lists those targets. |

The following commands describe memorial dataset collectors. They are not
currently registered Cargo gates and must not be used as acceptance counts:

- `cargo test --release run_gsm8k_solutions -- --ignored --nocapture`
- `cargo test --release run_metamathqa_litex_solutions -- --ignored --nocapture`
- `cargo test --release run_minif2f_litex_finished -- --ignored --nocapture`
- `cargo test --release run_math500_tmp -- --ignored --nocapture`
- `cargo test --release run_math500_litex_simple -- --ignored --nocapture`
- `cargo test --release run_math500_litex_all -- --ignored --nocapture`

Workspace-owned textbook tooling is in `scripts/textbook_gate.py`; the
predeploy entry is `.github/scripts/predeploy_gate.py`. Textbook files use the
current `-f` entry and checked `run` JSON contract. Its corpus filters still
need real collectors; a successful scoped gate does not certify this whole entry.

```text
collect registered examples and Markdown fences
  -> group independent inputs
  -> run groups with large stacks
  -> keep exact file/fence labels for failures
  -> report per-item and wall-clock timing
  -> fail if any collected example returns an error
```

Start with the docs fence runner
[`tests/tooling/run_docs_markdown_files.py`](tooling/run_docs_markdown_files.py)
and the phase tracers under `examples/`. Older references to a Cargo test named
`run_docs_markdown_files` describe the memorial legacy harness, not the current
crate.
