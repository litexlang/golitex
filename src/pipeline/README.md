# Running Litex source

`litex -e '1 + 1 = 2'`, `litex -f example.lit`,
`litex -isolated -f example.lit`, and `litex -r project` enter through explicit
code, automatic-file, forced-isolated-file, and repository functions. Graph
commands render the resulting `RunOutcome` without redispatching the input.

```text
run_code(source, options)         -> Runtime::new -> execute source
run_file(path, options)           -> select direct-parent project or isolated context
                                  -> Runtime::new -> execute selected file mode
run_isolated_file(path, options)  -> Runtime::new -> resolve and execute isolated file
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
| `litex -f chapter.lit` | Uses the direct-parent project when configured; otherwise runs the file in isolation. It exits after either batch run. |
| `litex -isolated -f scratch.lit` | Forces one isolated batch run and exits. |
| `litex -r std/basics` | Runs the module's recursive export tree. |
| `litex -session -f chapter.lit` | Uses project context when `chapter.lit` has a same-folder `litex.config`, otherwise isolation, then accepts framed statements. |
| `litex -f litex.config` | Rejected because configuration is not executable Litex source. |

## Start here

| File | Example |
| --- | --- |
| [`target.rs`](target.rs) | Models batch, REPL, distinct project-file and isolated-file targets, and their canonical source labels. |
| [`run.rs`](run.rs) | Owns the explicit code, automatic-file, forced-isolated-file, and repository batch entries, Runtime creation, and their shared outcome rendering. The canonical `RunOptions` lives in [`../runtime/run_options.rs`](../runtime/run_options.rs). |
| [`source_execution.rs`](source_execution.rs) | Tokenizes, parses, and executes source inside an already initialized Runtime. |
| [`file_execution.rs`](file_execution.rs) | Selects file context from the direct-parent `litex.config` and owns distinct project-file and isolated-file execution functions. |
| [`output_rendering.rs`](output_rendering.rs) | Renders statement results, errors, and JSONL stream envelopes. |
| [`terminal_import.rs`](terminal_import.rs) | Parses REPL-only `import` commands before source parsing and mutates the terminal's ephemeral module manifest. |
| [`repository_execution.rs`](repository_execution.rs) | Runs ordered project imports, module trees, file targets, and registered prefixes. |
| [`session.rs`](session.rs) | Keeps one runtime alive for `-session`. |
| [`summary.rs`](summary.rs) | Builds summaries requested by embedding APIs and internal artifacts; the CLI has no summary flag. |
