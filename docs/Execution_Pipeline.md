# Litex execution pipeline

For the command below, the main production path has one owned entry at each
boundary:

```bash
litex -e "1 + 1 = 2"
```

```text
main
  cli::run_cli
  cli::run_code_command
  pipeline::run
  Runtime::new(output_style, strict_mode, output_language)
  Runtime::start_isolated_source(source_label)
  Runtime::execute_source(source, SourceImportPolicy::UseRuntimePolicy)
  Runtime::execute_source_blocks
  Tokenizer::parse_blocks
  Runtime::parse_statement
  Runtime::execute_top_level_statement
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
| Batch pipeline | `pipeline::run(RunRequest)` | Owns code/file/repository dispatch, creates one Runtime, and renders once. |
| Runtime construction | `Runtime::new(output_style, strict_mode, output_language)` | Creates state and run configuration atomically. `Runtime::default()` is reserved for an explicit default configuration, especially tests and internal scratch runtimes. |
| Source execution | `Runtime::execute_source` | Requires an active source frame, tokenizes the source, and executes its blocks. `SourceImportPolicy` is the one case distinction: normal Runtime policy or compiler rejection of inline imports. |
| Parse | `Tokenizer::parse_blocks`, then `Runtime::parse_statement` | Converts source text into token blocks and typed statements. |
| Execute | `Runtime::execute_top_level_statement`, then `Runtime::execute_statement` | Handles top-level imports, resets statement-local proof state, and dispatches verified or configured trusted-import execution. |
| Verify | `Runtime::verify_fact_or_error` | Produces proof evidence or a structured RuntimeError. |
| Result | `Runtime::finish_statement_execution` | Attaches FactIds and execution provenance to the finished `StmtResult`. |
| Output | `pipeline::render_run_output` | Renders the statement Results and any RuntimeError. |
| Lean compiler | `compile_litex_source_to_lean_source`, then `StmtResultToLeanCompiler::compile_stmt_results_to_lean_source` | Runs the same Runtime source path with `SourceImportPolicy::Reject`, then consumes verified Results. |

## Why `source_label` exists

Inline `-e` source has no filesystem path, but parser and Runtime errors still
need a source identity. `RunTarget::Code.source_label` supplies that synthetic
name (`-e`, `-runner -e`, and similar values). Runner JSON preserves the public
key `target.label`; for code it contains this source label, while file and
repository targets use their display path/name. Hiding file paths changes only
non-code runner labels to `entry`.

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
