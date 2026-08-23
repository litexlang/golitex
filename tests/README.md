# Repository test harnesses

`cargo test --release run_examples -- --nocapture` runs registered examples and the repository's executable Markdown snippets. The white-box harness is stored under `tests/kernel_contracts/` and is loaded as a private `#[cfg(test)]` module, so it can check crate-internal contracts without becoming part of the production `src` tree or public API.

## Examples and boundaries

| Command | Actual coverage example |
| --- | --- |
| `cargo test --release run_examples_only -- --nocapture` | Runs the selected `.lit` example dataset without the remaining docs phase. |
| `cargo test --release run_docs_markdown_files -- --nocapture` | Runs root `README.md` plus `docs/**/*.md` Litex fences. |
| `cargo test --release runtime_contract_builtin_and_clear -- --nocapture` | Runs the checked-`1 = 1` and `clear` runtime smoke test. |
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

Start with [`kernel_contracts/lit_file_runner_tests/examples_runner.rs`](kernel_contracts/lit_file_runner_tests/examples_runner.rs); for example, `run_examples` and `run_docs_markdown_files` are separate gates. Compiler white-box regressions live in [`kernel_contracts/stmt_result_to_lean_compiler.rs`](kernel_contracts/stmt_result_to_lean_compiler.rs), compiler result tracers live in [`stmt_result_to_lean_compiler_tracers.rs`](stmt_result_to_lean_compiler_tracers.rs), and structural JSON black-box regressions live in [`result_json_v2.rs`](result_json_v2.rs).
