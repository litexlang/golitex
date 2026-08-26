# Litex source map

The source tree turns `1 + 1 = 2` into a checked `StmtResult` and a machine-readable runner result.

## Main execution spine

The shortest map of the primary source path is:

```text
main → CLI → pipeline → Runtime → parse → execute → verify → Result → Lean compiler
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
| CLI command | [`cli::run_code_command()`](cli/command_handlers.rs) | Adapts the selected `-e` target to the shared batch request. File, repository, and runner commands have parallel handlers in the same file. |
| Batch pipeline | [`pipeline::run(RunRequest)`](pipeline/run.rs) | Owns the code/file/repository batch entry and creates the `Runtime`. |
| Runtime state | [`Runtime::new(output_style, strict_mode, output_language)`](runtime/state.rs) | Creates the environment, module state, proof state, identifiers, and run options together; `Runtime::default()` is the explicit default/test configuration. |
| Source pipeline | [`Runtime::execute_source`](pipeline/source_execution.rs) | Tokenizes and executes statement blocks in order on the Runtime that owns their state. |
| Parse | [`Tokenizer::parse_blocks`](parse/tokenizer.rs) and [`Runtime::parse_statement`](parse/statement_parsing.rs) | Turn source text into `TokenBlock` values and then typed `Stmt` values. |
| Execute | [`Runtime::execute_top_level_statement`](pipeline/top_level_statement_execution.rs) and [`Runtime::execute_statement`](execute/statement_execution.rs) | Dispatch a statement, clear statement-local proof state, and select verified or configured trusted-import execution. |
| Verify | [`Runtime::verify_fact_or_error`](verify/dispatch.rs) | Dispatches fact verification; equality reaches [`Runtime::verify_equal_fact`](verify/equality/core.rs). |
| Result | [`Runtime::finish_statement_execution`](execute/statement_execution.rs) | Attaches FactIds and execution provenance, then returns the completed [`StmtResult`](result/statement/result.rs). |
| Lean compiler | [`compile_litex_source_to_lean_source`](stmt_result_to_lean_compiler/source_compilation.rs) and [`StmtResultToLeanCompiler::compile_stmt_results_to_lean_source`](stmt_result_to_lean_compiler/implementation/result_dispatch.rs) | Optionally replay verified Results as Lean declarations and proof terms. |

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
| Every nonempty top-level source subsystem has one README. | `parse/README.md` documents parsing, while `bin/README.md` documents the standalone compiler-maintenance binary. |
| Start with an observable input and result. | `verify/README.md` starts from `1 + 1 = 2`, not from a list of Rust types. |
| Put every capability beside its nearest boundary. | `rational_expression/README.md` pairs `x ^ 2 / x = x` with the required premise `x != 0`. |
| Add pseudocode only for an important control flow or algorithm. | `pipeline/README.md` shows the parse/execute loop; `common/README.md` only shows concrete helpers. |
| Link the real implementation entry point. | `execute/README.md` links `statement_execution.rs`; it does not duplicate that file line by line. |

## Subsystems

| Directory | Concrete example |
| --- | --- |
| [`bin/`](bin/README.md) | `stmt_result_to_lean_compiler check lean/examples` checks generated-source drift and invokes Lean. |
| [`cli/`](cli/README.md) | `litex -runner -e '1 + 1 = 2'` selects the runner command. |
| [`common/`](common/README.md) | `FactId::new(12)` displays as `f12`. |
| [`environment/`](environment/README.md) | After checking `a = 1`, later statements can reuse that equality. |
| [`error/`](error/README.md) | `1 / 0 = 0` becomes a well-definedness error. |
| [`execute/`](execute/README.md) | `1 + 1 = 2` is verified and then stored. |
| [`fact/`](fact/README.md) | `1 = 1`, `1 = 1 and 2 = 2`, and the README's two-line `forall x R:` example are different `Fact` variants. |
| [`graph/`](graph/README.md) | `litex -graph -e '1 = 1' graph.json` exports the result dependency graph. |
| [`infer/`](infer/README.md) | Storing `1 = 1 and 2 = 2` also stores its two components. |
| [`module_manager/`](module_manager/README.md) | `[export] main = "./main.lit"` orders a module file. |
| [`obj/`](obj/README.md) | `x + 1`, `sin(x)`, and `{1, 2}` become `Obj` variants. |
| [`output/`](output/README.md) | A checked `1 = 1` renders as statement-result JSON v2. |
| [`parse/`](parse/README.md) | The README's two-line `forall x R:` example becomes a `ForallFact` statement. |
| [`pipeline/`](pipeline/README.md) | `-f`, `-r`, and `-e` share one parse/execute/render pipeline. |
| [`rational_expression/`](rational_expression/README.md) | `(1 + i) * (1 - i) = 2` uses complex algebraic normalization. |
| [`result/`](result/README.md) | `1 + 1 = 2` retains the calculation proof route. |
| [`runner/`](runner/README.md) | A successful run has top-level `"ok": true`. |
| [`runtime/`](runtime/README.md) | One run owns its module stack, FactId allocator, and temporary proof guards. |
| [`stmt/`](stmt/README.md) | `have a R = 1` and `1 = 1` become different `Stmt` variants. |
| [`stmt_result_to_lean_compiler/`](stmt_result_to_lean_compiler/README.md) | The complex calculation example is replayed as Lean proof code. |
| [`symbol/`](symbol/README.md) | Two nested binders named `x` receive different `SymbolId` values. |
| [`to_latex/`](to_latex/README.md) | `litex -latex -e '1 = 1'` renders LaTeX. |
| [`to_python/`](to_python/README.md) | `litex -python -e '1 = 1'` uses the frozen Python extractor. |
| [`verify/`](verify/README.md) | `x ^ 2 / x = x` needs `x != 0` before algebraic verification. |

## Repository tests

Cross-subsystem contracts, example runners, dataset gates, and compiler tracers live outside the production library under [`../tests/`](../tests/README.md). Unit tests that need private implementation details remain beside their owning subsystem.
