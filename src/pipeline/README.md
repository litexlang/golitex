# Running Litex source

`litex -runner -e '1 + 1 = 2'` and `litex -f example.lit` share the same source-to-result pipeline.

```text
run_source_code(source, runtime)
  blocks = Tokenizer.parse_blocks(source)
  for block in blocks:
    stmt = runtime.parse_stmt(block)
    result = run_stmt_at_global_env(runtime, stmt)
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
| [`pipeline.rs`](pipeline.rs) | Selects code, file, or repository execution for `-e`, `-f`, and `-r`. |
| [`pipeline_run_stmt_globally.rs`](pipeline_run_stmt_globally.rs) | Runs each parsed statement in the global environment. |
| [`pipeline_session.rs`](pipeline_session.rs) | Keeps one runtime alive for `-session`. |
| [`summary.rs`](summary.rs) | Builds the optional `-summarize` output. |

