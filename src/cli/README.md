# Command-line interface

`litex -e '1 + 1 = 2'` executes inline source through the shared batch entry.

```text
args = parse global fields (-compact, -strict, -lang, ...)
match first command:
  -e/-f/-r -> enter the matching run_*_command handler
             -> call pipeline::run_code/run_file/run_repository
  -runner  -> enter run_runner_command
             -> execute the selected entry and render its RunOutcome
  graph commands -> execute the selected entry and render its RunOutcome
  -latex   -> render LaTeX
  -extractpython/-extractc -> verify and extract the supported executable subset
invalid combination -> print help and exit 2
```

## Examples and boundaries

| Command | Behavior |
| --- | --- |
| `litex -e '1 = 1'` | Executes inline Litex. |
| `litex -compact -runner -f example.lit` | Emits one compact runner wrapper for a file. |
| `litex -lang zh-Hans -e '1 = 2'` | Selects Simplified Chinese diagnostics such as `验证错误`; `zh-Hant` selects Traditional Chinese. |
| `litex -compact -detail -e '1 = 1'` | Rejected because compact and detailed output conflict. |
| `litex -strict -f example.lit` | Verifies configured dependencies and rejects source-level trust or axioms. |

## Start here

| File | Responsibility |
| --- | --- |
| [`command_dispatch.rs`](command_dispatch.rs) | `run_cli` selects one command and preserves its exit behavior. |
| [`arguments.rs`](arguments.rs) | Removes and validates global flags directly into the runtime-owned `RunOptions`. |
| [`command_handlers.rs`](command_handlers.rs) | Owns command-level adapters such as `run_code_from_e_command_line_flag`, calls the matching explicit pipeline entry, and hands its outcome to runner or graph rendering while preserving process behavior. |
| [`lean_commands.rs`](lean_commands.rs) | Validates and executes single-file Lean and Markdown-ledger compilation commands. |
| [`conversion_commands.rs`](conversion_commands.rs) | Owns complete `-latex`, `-extractpython`, and `-extractc` command handling and their adapters. |
| [`messages.rs`](messages.rs) | Owns stable help and upgrade text. |

These entry files name dependencies from `graph`, `pipeline`, `runner`, and
`runtime` explicitly. They intentionally do not use the kernel-wide prelude,
so a reader can follow each imported command directly to its owner.
