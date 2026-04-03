# Litex command-line interface (Rust kernel)

This document matches the entry behavior in `src/cli.rs` and explains how to invoke the `litex` binary from a terminal.

## Basic usage

- **No arguments**: starts the interactive REPL (see `-help`).
- **With options**: parsed as described below; unknown arguments print an error and exit with code `2`.

The executable is usually the `litex` binary built with Cargo (or whatever name you install under). In examples we write:

```text
litex [OPTION...]
```

---

## Options

| Option | Description |
|--------|-------------|
| `-help` | Print help and exit. |
| `-version` | Print version (`litex` and `CARGO_PKG_VERSION`) and exit. |
| `-e <code>` | Run a source string (loads the builtin environment first, then runs your code). |
| `-f <file>` | Run a file (path may be relative to the current working directory or absolute). |
| `-r <repo>` | Same as running `<repo>/main.lit` (place `main.lit` at the repo root). |
| `-latex` | LaTeX-related; with no further arguments, interactive LaTeX mode (often a stub message in the Rust kernel). |
| `-latex -f <file>` | Compile a file to LaTeX (stub message if not implemented). |
| `-latex -e <code>` | Compile code to LaTeX (same). |
| `-latex -r <repo>` | Compile the repo (`main.lit`) to LaTeX (same). |
| `-fmt <code>` | Format code (stub if not implemented). |
| `-install <module>` | Install a module (stub if not implemented). |
| `-uninstall <module>` | Uninstall a module (same). |
| `-list` | List installed modules (same). |
| `-update <module>` | Update a module (same). |
| `-tutorial` | Run the tutorial (same). |

Options like `-e`, `-f`, `-r`, `-fmt`, `-install`, `-uninstall`, and `-update` require a **value that does not start with `-`** immediately after the flag. After `-latex`, you may use sub-options `-f`, `-e`, or `-r` with their arguments.

---

## Successful runs and JSON: the `result` field

For paths that actually execute user source—**`-e`** and **`-f` / `-r`** (file runs)—the runtime emits one JSON object per successfully executed statement (see `render_run_source_code_output` and `Runtime::display_result_json_string`).

If the **full pipeline succeeds** (builtin environment runs, then user source parses and runs without error):

- The output contains **one JSON object per user statement**, separated by newlines; each object describes that statement’s outcome.
- In each such **successful** statement object, there is a **`"result"`** field.
- When everything succeeds, the JSON for the **last statement in your source** has **`"result": "success"`** (same constant as in `runtime_display_result.rs`).

So in the success case, the **last statement-result JSON block** should include `"result": "success"`. Earlier statement blocks also use `"success"` when those statements succeed.

e.g.

```json
{
  "result": "success",
  "stmt_type": "DefPropStmt",
  "line": 1,
  "source": "~/tmp.lit",
  "stmt": "prop group_property(s set, zero s, add fn (x, y s) s, inv fn (x s) s):\n    forall x, y, z s:\n        add(x, add(y, z)) = add(add(x, y), z)\n    forall x s:\n        add(x, zero) = x\n        add(zero, x) = x\n        add(x, inv(x)) = zero\n        add(inv(x), x) = zero",
  "infer_facts": [],
  "inside_results": []
}
```

If a runtime error occurs, an **error** JSON object is appended after the statement JSON; its `"result"` is usually **`"error"`** (see `runtime_display_error.rs`). The process may exit non-zero (e.g. `1` if builtin setup fails, `2` for bad arguments on `-e`). Parsers should not rely on the exit code alone—check for error JSON as well.

e.g.

```json
{
  "error_type": "VerifyError",
  "result": "error",
  "line": 1,
  "source": "~/tmp.lit",
  "message": "1 = 0",
  "previous_error":
  {
    "error_type": "UnknownError",
    "result": "error",
    "line": 1,
    "source": "~/tmp.lit",
    "message": "1 = 0",
    "previous_error": null
  }
}

```

---

## Stubs vs. real JSON output

`-latex`, `-fmt`, module management, `-tutorial`, etc. may still print **plain-text placeholder messages** in the Rust kernel instead of the JSON stream described above; treat `src/cli.rs` as the source of truth.

---

## Related source files

- Argument parsing and stubs: `src/cli.rs`
- Concatenating per-statement JSON: `render_run_source_code_output` in `src/pipeline/pipeline.rs`
- Success JSON: `src/runtime/runtime_display_result.rs`
- Error JSON: `src/runtime/runtime_display_error.rs`
