# Machine runner envelope

`litex -runner -e '1 + 1 = 2'` returns one wrapper JSON object whose top-level `ok` is `true`.

```json
{
  "runner": "litex-runner",
  "runner_version": "0.1",
  "result": "success",
  "ok": true,
  "target": {"kind": "code", "label": "-runner -e"},
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
run_runner(RunnerRequest)
  -> pipeline::run(RunRequest)
  -> collect (ok, statement-result trace)
  -> wrap target metadata, error, and trace once
  -> optionally attach structured pipeline_trace
  -> return wrapper JSON and the same boolean as the process status
```

Start with [`target_execution.rs`](target_execution.rs). `run_runner` is the only
runner entry; code, file, and repository differences live in
`RunRequest.target`, while strictness, language, isolation, output style, and
pipeline tracing live in `RunRequest.options`.
