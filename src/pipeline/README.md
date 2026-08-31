# Running Litex source

`litex -e '1 + 1 = 2'`, `litex -f example.lit`, and `litex -r project`
enter through separate code, file, and repository functions. Runner and graph
commands render the resulting `RunOutcome` without redispatching the input.

```text
run_code(source, options)         -> Runtime::new -> execute source
run_file(path, options)           -> Runtime::new -> resolve and execute file
run_repository(path, options)     -> Runtime::new -> discover and execute repository
                                   -> render output and optional summary once
```

Each outcome retains one typed `RunTarget`. Project versus isolated file
execution is part of that target; repository discovery identifiers remain
internal to the module system.

The files on this path import their dependency owners directly. Reading from
`run.rs` into `source_execution.rs`, `statement_parsing.rs`, and the executor
therefore shows whether a type comes from `runtime`, `stmt`, `result`, `error`,
or `module_manager` without first expanding the crate-wide prelude.

## Examples and boundaries

| Entry point | Pipeline behavior |
| --- | --- |
| `litex -e '1 = 1'` | Runs source code in an isolated runtime. |
| `litex -f chapter.lit` | Discovers project context and runs the registered prefix through that file. |
| `litex -isolated -f scratch.lit` | Runs one standalone file and continues in the same isolated REPL runtime. |
| `litex -r std/basics` | Runs the module's recursive export tree. |
| `litex -session -f chapter.lit` | Runs a verified registered prefix through the target and then accepts framed statements. |
| `litex -f litex.config` | Rejected because configuration is not executable Litex source. |

## Start here

| File | Example |
| --- | --- |
| [`target.rs`](target.rs) | Models batch, REPL, file-mode, and session targets and their canonical source labels. |
| [`run.rs`](run.rs) | Owns the explicit batch entries, Runtime creation, and their shared outcome rendering. The canonical `RunOptions` lives in [`../runtime/run_options.rs`](../runtime/run_options.rs). |
| [`source_execution.rs`](source_execution.rs) | Tokenizes, parses, and executes source inside an already initialized Runtime. |
| [`file_execution.rs`](file_execution.rs) | Resolves `-f`, discovers project context, and selects repository-prefix or isolated-file execution. |
| [`output_rendering.rs`](output_rendering.rs) | Renders statement results, errors, and unverified-import warnings. |
| [`terminal_import.rs`](terminal_import.rs) | Parses REPL-only `import` commands before source parsing and mutates the terminal's ephemeral module manifest. |
| [`repository_execution.rs`](repository_execution.rs) | Runs ordered project imports, module trees, file targets, and registered prefixes. |
| [`session.rs`](session.rs) | Keeps one runtime alive for `-session`. |
| [`summary.rs`](summary.rs) | Builds the optional `-summarize` output. |
