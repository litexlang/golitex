# Litex execution pipeline

Batch verification has one owned entry:

```rust
pub fn run(request: RunRequest) -> RunOutcome
```

It lives in `src/pipeline/run.rs`. `RunRequest.target` is one of
`RunTarget::Code`, `RunTarget::File`, or `RunTarget::Repository`, while
`RunRequest.options` carries output style, strictness, language, summary,
isolation, and trusted-prefix choices. Target and option combinations
are handled inside `run`; they are not encoded as function-name combinations.

The main file boundaries are:

```text
run.rs
  -> file_execution.rs or source_execution.rs or repository_execution.rs
  -> parse -> execute -> well-definedness -> verify -> store -> StmtResult
  -> output_rendering.rs
  -> optional StmtResult-to-Lean compiler
```

## Before and now

Before this cleanup, callers had to choose among overlapping code/file/repo,
strict, output, language, and isolation wrappers. The runner alone exposed 10
top-level run functions; graph execution had 37 result/fact/definition entry
variants; source execution included 12 compatibility wrappers in addition to
its main entry ladder; REPL exposed 8 run variants; session exposed 2; and run
summary rendering exposed 3 variants.

Now:

- batch verification uses `run(RunRequest)`;
- runner uses `run_runner(RunnerRequest)`;
- graph execution uses `run_graph(GraphRequest)` plus distinct schema
  renderers;
- session uses `run_session(SessionRequest)`;
- REPL uses `run_repl(version, ReplOptions)`; persistent-runtime and LaTeX
  REPL boundaries remain explicit;
- summary output uses `render_run_summary(RunSummaryRequest)`;
- the old compatibility modules and pure forwarding aliases are deleted;
- the unused fourth boolean parameter of `render_run_output` was removed from
  656 call sites.

The break is intentional. The retired public functions were not deprecated or
kept as aliases.

## Static path for one statement

The following is a source-reading map for the representative statement
`1 + 1 = 2`. It identifies major architectural interfaces; it is not emitted
by a CLI flag and is not a runtime or JSON output contract.

```text
1. main — src/main.rs
2. cli::run_cli — src/cli/command_dispatch.rs
3. cli::run_code_command — src/cli/command_handlers.rs
4. pipeline::run — src/pipeline/run.rs
5. Runtime::new — src/runtime/state.rs
6. pipeline::execute_source — src/pipeline/source_execution.rs
7. pipeline::execute_source_with_options — src/pipeline/source_execution.rs
8. Tokenizer::parse_blocks — src/parse/tokenizer.rs
9. Runtime::parse_statement — src/parse/statement_parsing.rs
10. pipeline::execute_top_level_statement — src/pipeline/top_level_statement_execution.rs
11. Runtime::execute_statement — src/execute/statement_execution.rs
12. Runtime::execute_verified_statement — src/execute/verified_statement_execution.rs
13. Runtime::execute_submitted_fact — src/execute/submitted_fact_execution.rs
14. Runtime::verify_fact_well_defined_for_execution — src/execute/submitted_fact_execution.rs
15. Runtime::verify_atomic_fact — src/verify/atomic/core.rs
16. Runtime::verify_fact_for_execution — src/execute/submitted_fact_execution.rs
17. Runtime::verify_fact_or_error — src/verify/dispatch.rs
18. Runtime::verify_equal_fact — src/verify/equality/core.rs
19. Runtime::store_executed_fact_and_infer — src/execute/submitted_fact_execution.rs
20. Runtime::finish_statement_execution — src/execute/statement_execution.rs
21. pipeline::render_run_output — src/pipeline/output_rendering.rs
```

The ordering summarizes the main call path and omits recursive helper calls.
`Runtime::verify_atomic_fact` can first be entered while checking
well-definedness, before the outer `Runtime::verify_fact_for_execution` route.

The source files on this main path now import their owning modules explicitly.
Statement execution also names its two independent axes: `ExecutionMode`
selects verified versus trusted execution, while `StatementExecutionContext`
selects an ordinary versus trusted-prefix run. These were previously passed as
booleans at the most important navigation boundary.

Ordinary verification stops after rendering the `StmtResult`. Single-file
Litex-to-Lean compilation is a separate explicit command:

```text
target/release/litex -isolated -f input.lit -lean output.lean
```

The compiler reuses `execute_source_with_options` for tokenization, parsing,
execution, and verification before consuming verified `StmtResult` values. Its
source path continues through `compile_litex_source_to_lean_source` and
`StmtResultToLeanCompiler::compile_stmt_results_to_lean_source`. Single-file
compilation still rejects source `import` statements with its existing
diagnostic.

## Stable semantic boundaries

The unified batch entry does not merge responsibilities merely to reduce the
function count. These remain separate because they own different invariants:

- `Tokenizer::parse_blocks` and `Runtime::parse_statement` own parsing;
- `Runtime::execute_statement` and statement-specific dispatch own execution;
- well-definedness and proof-producing verifier functions own verification;
- `Runtime::finish_statement_execution` owns the finished `StmtResult`;
- the Lean compiler consumes verified results and does not reimplement source
  execution.

`execute_source(source, runtime)` is intentionally retained for callers that
own an already initialized `Runtime`, including persistent REPL/session flows.
File and repository execution also keep lower-level functions because they own
project discovery, imports, and execution-layer invariants. These are semantic
boundaries, not alternate batch entries.

## Verification evidence

The final 2026-08-24 state passed:

- `cargo fmt --all -- --check`;
- `cargo check --release` and `cargo build --release`;
- `cargo test --release`: the library reported 1,139 passed and 8 explicitly
  ignored, followed by all binary, integration, showcase, and doc tests with no
  failures;
- `cargo test --release run_all_docs_examples_runtime_contracts -- --ignored
  --nocapture`: 1 passed, covering 333 documentation Litex blocks, 123 selected
  example or ledger groups, and runtime contract smoke tests;
- focused curated-public-API, runner, graph, CLI, summary, and compiler suites.

The briefly introduced `-trace-pipeline` experiment was removed. The retired
CLI regression requires that spelling to be rejected as an unknown argument,
and runner JSON has no Rust pipeline-trace field.

The removal was checked with the retired-command integration test, 31 CLI unit
tests, 10 runner unit tests, the curated public-API and source-architecture
tests, and the compiler CLI, 68 compiler tracer, and Markdown compiler suites.
The release binary still accepts `-e "1 + 1 = 2"` and rejects the retired flag
with exit code 2.

Real Lean kernel replay was not rerun: this change altered the source-to-result
producer route, not generated Lean representation or proof semantics. The 68
compiler tracer tests, compiler CLI transactional tests, checked-in output
reproduction, and Markdown compiler tests were run instead.

## Adjacent smells not hidden by this cleanup

- The crate-wide prelude remains broad outside the main execution spine, so
  unrelated leaf subsystems can still see more APIs than their ownership
  boundary requires.
- `RunOutcome` carries both structured results/runtime state and rendered
  output, while target-resolution errors and runtime errors remain separate
  channels. Unifying that error/result model would be a separate API decision.
- Release builds report five existing dead-code warning groups in
  `src/verify/well_definedness/object/`; they are unrelated to the execution
  entry ladder and were not silently deleted.
- `discover_repository_for_file` contains `_for_file` in its name but is not a
  forwarding variant: it performs file-to-project discovery and has different
  invariants from repository-root discovery.
