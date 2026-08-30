# Litex execution pipeline

For the command below, the main production path has one owned entry at each
boundary:

```bash
litex -e "1 + 1 = 2"
```

```text
main
  cli::run_cli
  cli::run_code_from_e_command_line_flag
  pipeline::run_code
  Runtime::new(options: RunOptions)
  Runtime::start_isolated_source("<-e>")
  Runtime::execute_source(source)
  Runtime::execute_source_blocks
  Tokenizer::parse_blocks
  Runtime::parse_statement
  Runtime::execute_statement
  Runtime::execute_verified_statement
  Runtime::execute_submitted_fact
  Runtime::verify_fact_well_defined_for_execution
  Runtime::verify_fact_for_execution
  Runtime::verify_fact_or_error
  Runtime::verify_equal_fact
  Runtime::store_executed_fact_and_infer
  Runtime::finish_statement_execution
  pipeline::render_run_output
```

This is a static source-reading map, not a tracing CLI option. The list keeps
the major interfaces and omits recursive verifier helpers. Well-definedness
may itself call atomic verification before the outer proof-verification step.

## Boundary ownership

| Boundary | Main interface | Responsibility |
| --- | --- | --- |
| Process | `main` in `src/main.rs` | Starts the CLI thread. |
| CLI | `cli::run_cli` | Parses global options and selects one command. |
| Batch pipeline | `pipeline::run_code`, `pipeline::run_file`, or `pipeline::run_repository` | Each explicit entry creates one Runtime, performs its input-specific setup, and renders once. |
| Runtime construction | `Runtime::new(options: RunOptions)` | Creates state and stores the one run configuration atomically. `Runtime::default()` is reserved for an explicit default configuration, especially tests and internal scratch runtimes. |
| Source execution | `Runtime::execute_source` | Requires an active source frame, tokenizes the source, and executes its blocks. `import` is never part of this grammar. |
| Parse | `Tokenizer::parse_blocks`, then `Runtime::parse_statement` | Converts source text into token blocks and typed statements. |
| Execute | `Runtime::execute_statement` | Resets statement-local proof state and dispatches verified or configured trusted execution. |
| Verify | `Runtime::verify_fact_or_error` | Produces proof evidence or a structured RuntimeError. |
| Result | `Runtime::finish_statement_execution` | Attaches FactIds and execution provenance to the finished `StmtResult`. |
| Output | `pipeline::render_run_output` | Renders the statement Results and any RuntimeError. |
| Lean compiler | `compile_litex_source_to_lean_source`, then `StmtResultToLeanCompiler::compile_stmt_results_to_lean_source` | Runs the same source-only Runtime path, then consumes verified Results. |

Interactive REPL input has one earlier terminal boundary. If the first token is
`import`, `pipeline::terminal_import` parses a terminal command and updates the
REPL's in-memory module manifest; it does not create a `Stmt` or `StmtResult`.
All other input enters `Runtime::execute_source`. The machine-framed `-session`
protocol is source-only and deliberately has no import frame.

## Internal source identity versus output label

Inline `-e` source has no filesystem path, but parser and Runtime errors still
need a source identity. `run_code` therefore starts inline execution with the
stable internal path `<-e>` and receives the source text directly.

Runner and graph adapters create their command-facing labels only while
rendering output: `-runner -e`, `-graph -e`, `-factgraph -e`, or `-defgraph -e`.
These display strings do not enter Runtime state. File and repository
outcomes retain an optional resolved `target_path` for output and file-target
selection; hidden non-code paths render as `entry`.

Target classification stays typed as `RunTargetKind` through pipeline,
runner, graph, and session artifact generation. The fixed JSON names `code`,
`file`, `repo`, and `session` are produced only by `RunTargetKind::json_name`
when an output document is built.

## Statement-local proof state

`Runtime::clear_statement_proof_state` clears transient memoized proofs and
recursion guards before and after one top-level statement. It deliberately
does not clear the Environment, definitions, stored facts, FactIds, or module
state. Without this boundary, a proof found while checking one statement could
be reused as if it were persistent mathematical knowledge in a later one.

## Local builtin rule catalog

`registered_local_builtin_rules` loads the generated Litex schemas for local
builtin theorems. The schemas are compiled once per thread and cached. The
statement executor initializes the catalog at the shallow statement boundary
so first use does not put schema parsing underneath a deep recursive verifier
stack; verifier searches then read the same cached catalog.

## Deliberately separate paths

File and repository orchestration remain separate from source execution
because they own project discovery, ordered imports/exports, module lifecycle,
and execution frames. Parsing, execution, verification, Result construction,
runner wrapping, graph rendering, and Lean compilation also remain separate
semantic boundaries. The cleanup removes forwarding aliases and special-case
entry ladders; it does not merge unrelated invariants into one function.

There is no `-trace-pipeline` command and no trusted-prefix line cutoff. For
iterative work on a registered file, use the persistent session workflow:

```bash
litex -session -before path/to/file.lit
```

Final acceptance still runs the complete file or repository through the normal
verified pipeline.
