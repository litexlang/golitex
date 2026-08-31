# Command-line interface

`litex -e '1 + 1 = 2'` executes inline source through the shared batch entry.

```text
args -> command::parse_cli_command
     -> validate one hardcoded command shape and exact argument count
     -> produce one resolved CliCommand with owned values and RunOptions
match typed command:
  Execute -> command_handlers::run_command
          -> select pipeline::run_code/run_file/run_repository once
  Graph   -> execute the resolved input and render its RunOutcome
  Latex/Extract/Lean -> run the selected typed conversion
invalid combination -> print one cli_error JSON object and exit 2
```

## Examples and boundaries

| Command | Behavior |
| --- | --- |
| `litex -e '1 = 1'` | Executes inline Litex. |
| `litex -f example.lit` | Runs one registered file with canonical detailed JSON output. |
| `litex -lang zh-Hans -e '1 = 2'` | Selects Simplified Chinese diagnostics such as `验证错误`; `zh-Hant` selects Traditional Chinese. |
| `litex -compact -e '1 = 1'` | Rejected because `-compact` is not a CLI option. |
| `litex -strict -f example.lit` | Verifies configured dependencies and rejects source-level trust or axioms. |

## Start here

| File | Responsibility |
| --- | --- |
| [`command.rs`](command.rs) | Parses the complete argv once into a legal `CliCommand`, including resolved values, targets, save paths, and execution options. |
| [`command_dispatch.rs`](command_dispatch.rs) | `run_cli` matches only typed commands and preserves their exit behavior. It does not interpret raw flags. |
| [`command_handlers.rs`](command_handlers.rs) | Owns the single typed batch adapter `run_command`, selects the matching explicit pipeline entry, and hands graph outcomes to graph rendering while preserving process behavior. |
| [`lean_commands.rs`](lean_commands.rs) | Executes an already validated single-file Lean compilation command. |
| [`conversion_commands.rs`](conversion_commands.rs) | Executes already resolved `-latex`, `-extractpython`, and `-extractc` inputs. |
| [`messages.rs`](messages.rs) | Owns stable help text. |
