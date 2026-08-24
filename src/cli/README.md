# Command-line interface

`litex -trace-pipeline -e '1 + 1 = 2'` executes inline source through the shared batch entry and prints the major Rust functions visited.

```text
args = parse global fields (-compact, -strict, -lang, -trace-pipeline, ...)
match first command:
  -e/-f/-r -> build RunRequest and call pipeline::run
  -runner  -> build RunnerRequest around the same RunRequest
  graph commands -> build GraphRequest around the same RunRequest
  -latex   -> render LaTeX
  -python  -> run the frozen Python extractor
invalid combination -> print help and exit 2
```

## Examples and boundaries

| Command | Behavior |
| --- | --- |
| `litex -e '1 = 1'` | Executes inline Litex. |
| `litex -compact -runner -f example.lit` | Emits one compact runner wrapper for a file. |
| `litex -lang zh-Hans -e '1 = 2'` | Selects Simplified Chinese diagnostics such as `验证错误`; `zh-Hant` selects Traditional Chinese. |
| `litex -compact -detail -e '1 = 1'` | Rejected because compact and detailed output conflict. |
| `litex -strict -trust-before-line 10 -f example.lit` | Rejected because strict mode cannot use a trusted prefix. |
| `litex -trace-pipeline -e '1 + 1 = 2'` | Preserves ordinary output, then prints the Rust path and `Lean compiler: not executed`. |
| `litex -trace-pipeline -runner -e '1 + 1 = 2'` | Adds a structured `pipeline_trace` field to the runner JSON. |

## Start here

| File | Responsibility |
| --- | --- |
| [`command_dispatch.rs`](command_dispatch.rs) | `run_cli` selects one command and preserves its exit behavior. |
| [`arguments.rs`](arguments.rs) | Removes and validates global flags into `CliOptions`. |
| [`command_handlers.rs`](command_handlers.rs) | Converts CLI targets into `RunRequest`, `RunnerRequest`, or `GraphRequest` and preserves process behavior. |
| [`lean_commands.rs`](lean_commands.rs) | Validates and executes single-file Lean and Markdown-ledger compilation commands. |
| [`conversion_commands.rs`](conversion_commands.rs) | Owns complete `-latex` and `-python` command handling and their compiler adapters. |
| [`messages.rs`](messages.rs) | Owns stable help and upgrade text. |

These entry files name dependencies from `graph`, `pipeline`, `runner`, and
`runtime` explicitly. They intentionally do not use the kernel-wide prelude,
so a reader can follow each imported command directly to its owner.
