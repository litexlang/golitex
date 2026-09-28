# Machine result-envelope library

`render_runner` is a Rust library adapter that converts an already completed
`RunOutcome` into one wrapper JSON object. It is not exposed as a CLI command.

```json
{
  "runner": "litex-runner",
  "runner_version": "0.2",
  "result": "success",
  "ok": true,
  "target": {"kind": "code"},
  "error": null,
  "trace": "...statement-result JSON..."
}
```

## Result boundaries

| Outcome | Contract |
| --- | --- |
| Successful `RunOutcome` | `ok: true` and the statement stream is stored in `trace`. |
| Failed verification | `ok: false` and the diagnostic stream remains in `trace`. |
| Target-loading error | A target error appears in `error`; `trace` is empty. |
| A successful wrapper with diagnostic text inside `trace` | Success is decided from top-level `ok`, not by searching the nested string. |

```text
pipeline::run_code/run_file/run_isolated_file/run_repository
  -> render_runner(RunOutcome)
  -> collect (ok, statement-result trace)
  -> wrap target metadata, error, and trace once
  -> return wrapper JSON and the same boolean as the process status
```

Start with [`target_execution.rs`](target_execution.rs). `render_runner` accepts
an already executed `RunOutcome`; code, file, and repository selection remains
at the embedding call site.

## Rust API example

An embedding that already has an `outcome: RunOutcome` can render the envelope
without adding a CLI command:

```rust
let (ok, json) = render_runner(outcome, true);
```

The boolean is the machine success result and `json` is the wrapper shown
above. Passing `true` keeps file paths out of the rendered target metadata.

The target kind remains a `RunTargetKind` until this JSON object is rendered.
Inline code therefore needs no synthetic label; its source keeps the stable
internal source label `eval`. Embedding callers choose whether target paths are
hidden; the CLI's canonical detailed projection includes available paths.
Command spellings never enter Runtime state.
