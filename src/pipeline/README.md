# Running Litex source

`litex -runner -e '1 + 1 = 2'` and `litex -f example.lit` share the same source-to-result pipeline.

```text
run_source_code(source, runtime)
  blocks = Tokenizer.parse_blocks(source)
  for block in blocks:
    stmt = runtime.parse_statement(block)
    result = execute_top_level_statement(stmt, runtime)
    collect result or stop at RuntimeError
  render results, errors, and optional summary
```

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
| [`source_execution.rs`](source_execution.rs) | Starts with the canonical `run_source_code` entry, then owns code, file, or repository execution for `-e`, `-f`, and `-r`, plus relative source-file target resolution. |
| [`source_execution/compatibility.rs`](source_execution/compatibility.rs) | Retains the former long-signature file/repository helpers without placing them in the canonical reading path. |
| [`top_level_statement_execution.rs`](top_level_statement_execution.rs) | Executes one parsed top-level statement and owns isolated terminal imports. |
| [`repository_execution.rs`](repository_execution.rs) | Runs ordered project imports, module trees, file targets, and registered prefixes. |
| [`pipeline_run_stmt_globally.rs`](pipeline_run_stmt_globally.rs) | Retains the former public module path as a compatibility facade only. |
| [`pipeline_session.rs`](pipeline_session.rs) | Keeps one runtime alive for `-session`. |
| [`summary.rs`](summary.rs) | Builds the optional `-summarize` output. |
