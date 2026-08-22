# Repository test harnesses

`cargo test --release run_examples -- --nocapture` runs registered examples and the repository's executable Markdown snippets.

## Examples and boundaries

| Command | Actual coverage example |
| --- | --- |
| `cargo test --release run_examples_only -- --nocapture` | Runs the selected `.lit` example dataset without the remaining docs phase. |
| `cargo test --release run_docs_markdown_files -- --nocapture` | Runs root `README.md` plus `docs/**/*.md` Litex fences. |
| `cargo test --release runtime_contract_builtin_and_clear -- --nocapture` | Runs the checked-`1 = 1` and `clear` runtime smoke test. |
| `cargo test --release run_all_docs_examples_runtime_contracts -- --ignored --nocapture` | Runs the explicit slow aggregate of examples, docs, and runtime contracts. |
| A test name containing `run_all` | Does not imply compiler, Lean, textbook, or packaging coverage unless that command lists those targets. |

```text
collect registered examples and Markdown fences
  -> group independent inputs
  -> run groups with large stacks
  -> keep exact file/fence labels for failures
  -> report per-item and wall-clock timing
  -> fail if any collected example returns an error
```

Start with [`lit_file_runner_tests/examples_runner.rs`](lit_file_runner_tests/examples_runner.rs); for example, `run_examples` and `run_docs_markdown_files` are separate gates.
