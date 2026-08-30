# Machine runner envelope

`litex -runner -e '1 + 1 = 2'` returns one wrapper JSON object whose top-level `ok` is `true`.

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

## Examples and boundaries

| Command | Contract |
| --- | --- |
| `litex -runner -e '1 = 1'` | `ok: true` and process exit code `0`. |
| `litex -runner -e '1 = 2'` | `ok: false` and a nonzero process exit code. |
| `litex -runner -f missing.lit` | A target error appears in `error`; `trace` is empty. |
| A successful wrapper with diagnostic text inside `trace` | Success is decided from top-level `ok`, not by searching the nested string. |

```text
pipeline::run_code/run_file/run_repository
  -> render_runner(RunOutcome)
  -> collect (ok, statement-result trace)
  -> wrap target metadata, error, and trace once
  -> return wrapper JSON and the same boolean as the process status
```

Start with [`target_execution.rs`](target_execution.rs). `render_runner` accepts
an already executed `RunOutcome`; code, file, and repository selection remains
at the CLI or embedding call site, while `RunOptions` carries strictness,
language, isolation, output style, and summary behavior.

The target kind remains a `RunTargetKind` until this JSON object is rendered.
Inline code therefore needs no synthetic label; its source keeps the stable
internal path `<-e>`. File and repository targets expose only `kind` by
default, while `-detail` adds their real `path`. Command spellings never enter
Runtime state.
