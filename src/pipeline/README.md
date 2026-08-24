# Running Litex source

`litex -e '1 + 1 = 2'`, `litex -f example.lit`, `litex -r project`, runner mode, and graph mode all enter through `run(RunRequest)`.

```text
run(RunRequest { target, options })
  create and configure Runtime once
  match target: Code | File | Repository
  execute_source(source, runtime)               # default options adapter
    execute_source_with_options(source, runtime)
    Tokenizer::parse_blocks
    Runtime::parse_statement
    execute_top_level_statement
    Runtime::execute_statement -> verify -> Result
  render output and optional summary once
```

The files on this path import their dependency owners directly. Reading from
`run.rs` into `source_execution.rs`, `statement_parsing.rs`, and the executor
therefore shows whether a type comes from `runtime`, `stmt`, `result`, `error`,
or `module_manager` without first expanding the crate-wide prelude.

## Examples and boundaries

| Entry point | Pipeline behavior |
| --- | --- |
| `litex -e '1 = 1'` | Runs source code in an isolated runtime. |
| `litex -f chapter.lit` | Discovers project context and runs the registered prefix through that file. |
| `litex -r std/basics` | Runs the module's recursive export tree. |
| `litex -session -before chapter.lit` | Preloads the registered prefix before the target and then accepts framed statements. |
| `litex -f litex.config` | Rejected because configuration is not executable Litex source. |

## Start here

| File | Example |
| --- | --- |
| [`run.rs`](run.rs) | Owns the single batch entry `run(RunRequest)`, its request/target types, Runtime creation, and target dispatch. |
| [`source_execution.rs`](source_execution.rs) | Tokenizes, parses, and executes source inside an already initialized Runtime. |
| [`file_execution.rs`](file_execution.rs) | Resolves `-f`, discovers project context, and selects repository-prefix or isolated-file execution. |
| [`output_rendering.rs`](output_rendering.rs) | Renders statement results, errors, trusted-prefix metadata, and unverified-import warnings. |
| [`top_level_statement_execution.rs`](top_level_statement_execution.rs) | Executes one parsed top-level statement and owns isolated terminal imports. |
| [`repository_execution.rs`](repository_execution.rs) | Runs ordered project imports, module trees, file targets, and registered prefixes. |
| [`pipeline_session.rs`](pipeline_session.rs) | Keeps one runtime alive for `-session`. |
| [`summary.rs`](summary.rs) | Builds the optional `-summarize` output. |
