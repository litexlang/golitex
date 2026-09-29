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

`cargo test --release run_examples -- --nocapture` runs registered examples and
the repository's executable Markdown snippets. The white-box harness is kept
outside the production tree while retaining access to crate-internal contracts.

## Examples and boundaries

| Command | Actual coverage example |
| --- | --- |
| `cargo test --release run_examples_only -- --nocapture` | Runs the selected `.lit` example dataset without the remaining docs phase. |
| `python3 tests/tooling/run_docs_markdown_files.py` | Runs root `README.md` plus `docs/**/*.md` Litex fences via `target/release/litex`. |
| `cargo test --release runtime_contract_builtin -- --nocapture` | Runs the checked-`1 = 1` runtime smoke test. |
| `cargo test --release run_all_docs_examples_runtime_contracts -- --ignored --nocapture` | Runs the explicit slow aggregate of examples, docs, and runtime contracts. |
| A test name containing `run_all` | Does not imply compiler, Lean, textbook, or packaging coverage unless that command lists those targets. |

The explicit dataset gates remain ignored by default:

- `cargo test --release run_gsm8k_solutions -- --ignored --nocapture`
- `cargo test --release run_metamathqa_litex_solutions -- --ignored --nocapture`
- `cargo test --release run_minif2f_litex_finished -- --ignored --nocapture`
- `cargo test --release run_math500_tmp -- --ignored --nocapture`
- `cargo test --release run_math500_litex_simple -- --ignored --nocapture`
- `cargo test --release run_math500_litex_all -- --ignored --nocapture`

Workspace-owned textbook coverage uses `python3 scripts/textbook_gate.py`; the parallel pre-deploy docs/examples/showcases gate uses `python3 .github/scripts/predeploy_gate.py`.

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
