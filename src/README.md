# Litex source map

The source tree turns `1 + 1 = 2` into a checked `StmtResult` and a machine-readable runner result.

## Main execution spine

The shortest map of the primary source path is:

```text
main → CLI → pipeline → Runtime → parsing → execution → verification → Result → Lean compiler
```

`Runtime` is the state owner carried through parsing, execution, verification,
and storage. `Result` is the completed semantic handoff: ordinary verification
renders it directly, while Litex-to-Lean compilation consumes it as proof
evidence. The Lean compiler is an optional branch, so an ordinary `-e` run
stops after rendering the Result.

| Boundary | Main Rust interface | Responsibility |
| --- | --- | --- |
| Process | [`main()`](main.rs) | Starts the CLI thread. |
| CLI | [`cli::run_cli()`](cli/command_dispatch.rs) | Parses flags and selects code, file, repository, runner, graph, or compiler execution. |
| CLI command | [`cli::run_code_from_e_command_line_flag()`](cli/command_handlers.rs) | Adapts the selected `-e` input to `run_code`. File, repository, and runner commands have parallel handlers in the same file. |
| Batch pipeline | [`pipeline::run_code`, `run_file`, `run_repository`](pipeline/run.rs) | Each explicit entry owns its input-specific setup and creates the `Runtime`. |
| Runtime state | [`Runtime::new(options: RunOptions)`](runtime/state.rs) | Creates the environment, module state, proof state, identifiers, and one run-options value together; `Runtime::default()` is the explicit default/test configuration. |
| Source pipeline | [`Runtime::execute_source`](pipeline/source_execution.rs) | Tokenizes and executes statement blocks in order on the Runtime that owns their state. |
| Parsing | [`Tokenizer::parse_blocks`](parsing/tokenizer.rs) and [`Runtime::parse_statement`](parsing/statement_parsing.rs) | Turn source text into `TokenBlock` values and then typed `Stmt` values. |
| Execution | [`Runtime::execute_statement`](execution/statement_execution.rs) | Clears statement-local proof state and dispatches verified or configured trusted execution. Interactive imports take a separate terminal-command path before parsing and never become statements. |
| Verification | [`Runtime::verify_fact_or_error`](verification/dispatch.rs) | Dispatches fact verification; equality reaches [`Runtime::verify_equal_fact`](verification/equality/core.rs). |
| Result | [`Runtime::finish_statement_execution`](execution/statement_execution.rs) | Attaches FactIds and execution provenance, then returns the completed [`StmtResult`](result/statement/result.rs). |
| Lean compiler | [`compile_litex_source_to_lean_source`](stmt_result_to_lean_compiler/source_compilation.rs) and [`StmtResultToLeanCompiler::compile_stmt_results_to_lean_source`](stmt_result_to_lean_compiler/compiler/result_dispatch.rs) | Optionally replay verified Results as Lean declarations and proof terms. |

### Follow one statement through the source

[`docs/Execution_Pipeline.md`](../docs/Execution_Pipeline.md) records the major
Rust interfaces for `1 + 1 = 2` as a static source-reading map. It is developer
documentation, not a runtime tracing command or public output contract.

## Public Rust API boundary

Rust embedders should start with [`api.rs`](api.rs), which re-exports the small execution, output, and Litex-to-Lean surface intended for external use. Existing subsystem paths remain available for compatibility. [`prelude.rs`](prelude.rs) is the broad kernel-internal convenience import required by repository code, not the recommended embedding API.

```litex
1 + 1 = 2
```

```text
source `1 + 1 = 2`
  -> parse: Stmt::Fact(EqualFact(...))
  -> execute: check well-definedness, then verify
  -> verify: RationalNormalization evidence
  -> environment: store the checked fact with a FactId
  -> result: StmtResult::Success(...)
  -> output/runner: {"ok": true, ...}
```

## README rule

| Rule | Example |
| --- | --- |
| Every nonempty top-level source subsystem has one README. | `parsing/README.md` documents parsing, while `stmt_result_to_lean_compiler/README.md` also documents its standalone maintenance command entry. |
| Start with an observable input and result. | `verification/README.md` starts from `1 + 1 = 2`, not from a list of Rust types. |
| Put every capability beside its nearest boundary. | `algebraic_normalization/README.md` pairs `x ^ 2 / x = x` with the required premise `x != 0`. |
| Add pseudocode only for an important control flow or algorithm. | `pipeline/README.md` shows the parse/execute loop; `syntax/README.md` only shows concrete conventions. |
| Link the real implementation entry point. | `execution/README.md` links `statement_execution.rs`; it does not duplicate that file line by line. |

## Subsystems

| Directory | Concrete example |
| --- | --- |
| [`cli/`](cli/README.md) | `litex -runner -e '1 + 1 = 2'` selects the runner command. |
| [`compatibility/`](compatibility/README.md) | `litex::common::fact_id::FactId` temporarily re-exports `litex::fact::id::FactId`. |
| [`environment/`](environment/README.md) | After checking `a = 1`, later statements can reuse that equality. |
| [`error/`](error/README.md) | `1 / 0 = 0` becomes a well-definedness error. |
| [`execution/`](execution/README.md) | `1 + 1 = 2` is verified and then stored. |
| [`fact/`](fact/README.md) | `1 = 1`, `1 = 1 and 2 = 2`, and the README's two-line `forall x R:` example are different `Fact` variants. |
| [`graph/`](graph/README.md) | `litex -graph -e '1 = 1' graph.json` exports the result dependency graph. |
| [`inference/`](inference/README.md) | Storing `1 = 1 and 2 = 2` also stores its two components. |
| [`module_system/`](module_system/README.md) | `[export] main = "./main.lit"` orders a module file. |
| [`object/`](object/README.md) | `x + 1`, `sin(x)`, and `{1, 2}` become `Obj` variants. |
| [`output/`](output/README.md) | A checked `1 = 1` renders as statement-result JSON v2. |
| [`parsing/`](parsing/README.md) | The README's two-line `forall x R:` example becomes a `ForallFact` statement. |
| [`pipeline/`](pipeline/README.md) | `-f`, `-r`, and `-e` share one parse/execute/render pipeline. |
| [`algebraic_normalization/`](algebraic_normalization/README.md) | `(1 + i) * (1 - i) = 2` uses complex algebraic normalization. |
| [`result/`](result/README.md) | `1 + 1 = 2` retains the calculation proof route. |
| [`runner/`](runner/README.md) | A successful run has top-level `"ok": true`. |
| [`runtime/`](runtime/README.md) | One run owns its module stack, FactId allocator, and temporary proof guards. |
| [`statement/`](statement/README.md) | `have a R = 1` and `1 = 1` become different `Stmt` variants. |
| [`stmt_result_to_lean_compiler/`](stmt_result_to_lean_compiler/README.md) | The complex calculation example is replayed as Lean proof code. |
| [`symbol/`](symbol/README.md) | Two nested binders named `x` receive different `SymbolId` values. |
| [`syntax/`](syntax/README.md) | `forall` is reserved, while `user_name` is a valid source identifier. |
| [`latex_renderer/`](latex_renderer/README.md) | `litex -latex -e '1 = 1'` renders LaTeX. |
| [`extract_code_of_other_languages_from_litex/`](extract_code_of_other_languages_from_litex/README.md) | `litex -extractpython 'have a R = 1'` and `litex -extractc 'have a R = 1'` render one verified executable subset through two target backends. |
| [`verification/`](verification/README.md) | `x ^ 2 / x = x` needs `x != 0` before algebraic verification. |

## Repository tests

Cross-subsystem contracts, example runners, dataset gates, and compiler tracers live outside the production library under [`../tests/`](../tests/README.md). Unit tests that need private implementation details remain beside their owning subsystem.
