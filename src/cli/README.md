# Command-line interface

`litex -compact -strict -runner -e '1 + 1 = 2'` selects compact output, strict trust policy, the runner envelope, and an inline source target.

```text
args = remove global flags (-compact, -strict, -lang, ...)
match first command:
  -e       -> run source text
  -f       -> run one file target
  -r       -> run a module target
  -runner  -> emit one machine wrapper
  -graph   -> emit graph JSON
  -factgraph -> emit fact-dependency JSON
  -defgraph  -> emit definition-dependency JSON
  -latex   -> render LaTeX
  -python  -> run the frozen Python extractor
invalid combination -> print help and exit 2
```

## Examples and boundaries

| Command | Behavior |
| --- | --- |
| `litex -e '1 = 1'` | Executes inline Litex. |
| `litex -compact -runner -f example.lit` | Emits one compact runner wrapper for a file. |
| `litex -lang zh -e '1 = 2'` | Selects Simplified Chinese diagnostics such as `验证错误`. |
| `litex -compact -detail -e '1 = 1'` | Rejected because compact and detailed output conflict. |
| `litex -strict -trust-before-line 10 -f example.lit` | Rejected because strict mode cannot use a trusted prefix. |

## Start here

| File | Responsibility |
| --- | --- |
| [`command_dispatch.rs`](command_dispatch.rs) | `run_cli` selects one command and preserves its exit behavior. |
| [`arguments.rs`](arguments.rs) | Removes and validates global flags into `CliOptions`. |
| [`command_handlers.rs`](command_handlers.rs) | Owns the Runtime/output lifecycle for inline code, file, repository, runner, and graph targets after dispatch. |
| [`conversion_commands.rs`](conversion_commands.rs) | Adapts `-latex` and `-python` targets to their compiler pipelines. |
| [`messages.rs`](messages.rs) | Owns stable help and upgrade text. |
