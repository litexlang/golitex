# Litex command-line interface

Jiachen Shen and The Litex Team, 2026-05-06. Email: litexlang@outlook.com

Try all snippets in browser: https://litexlang.com/doc/CLI

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/CLI.md

This page explains how to run Litex from a terminal.

## Basic usage

- **No arguments**: starts the interactive REPL.
- **With options**: runs code, files, repositories, or helper commands as described below.
- **Unknown options**: print an error message and exit.

In examples, the executable is written as:

```text
litex [OPTION...]
```

---

## Options

| Option | Description |
|--------|-------------|
| `-help` | Print help and exit. |
| `-version` | Print the Litex version and exit. |
| `-e <code>` | Run a Litex source string. |
| `-f <file>` | Run a file (path may be relative to the current working directory or absolute). |
| `-r <repo>` | Same as running `<repo>/main.lit` (place `main.lit` at the repo root). |
| `-latex` | Enter LaTeX-related mode. |
| `-latex -f <file>` | Compile a file to LaTeX, when available. |
| `-latex -e <code>` | Compile a source string to LaTeX, when available. |
| `-fmt <code>` | Format Litex code, when available. |
| `-install <module>` | Install a module, when available. |
| `-uninstall <module>` | Uninstall a module, when available. |
| `-list` | List installed modules, when available. |
| `-update <module>` | Update a module, when available. |
| `-tutorial` | Run the tutorial, when available. |

Options like `-e`, `-f`, `-r`, `-fmt`, `-install`, `-uninstall`, and `-update` require a **value that does not start with `-`** immediately after the flag. After `-latex`, you may use sub-options `-f`, `-e`, or `-r` with their arguments.

Hint: if your Litex code contains spaces, newlines, or shell-sensitive characters, wrap it in quotes when using `-e`, or put it in a `.lit` file and run it with `-f`.

---

## Output format

For commands that execute Litex source, such as **`-e`**, **`-f`**, and **`-r`**, Litex prints one JSON object for each executed statement.

If the whole run succeeds:

- The output contains **one JSON object per user statement**, separated by newlines; each object describes that statement’s outcome.
- Each successful statement object has `"result": "success"`.
- The last JSON object for your source is the last statement that ran successfully.

This is useful when another program wants to call Litex and inspect whether a proof or computation succeeded.

Example success output looks like this (may be different from the actual output):

```json
{
  "result": "success",
  "type": "DefPropStmt",
  "line": 1,
  "source": "~/tmp.lit",
  "stmt": "1 + 1 = 2",
  "infer_facts": [],
  "inside_results": []
}
```

If an error occurs, Litex prints an error JSON object. The important fields are usually:

- `"result": "error"`
- `"error_type"`: the broad kind of error, such as parse, verify, or runtime error
- `"message"`: the human-readable reason
- `"previous_error"`: more context, if the error was caused by another error

Hint: programs that call Litex should check the JSON output, not only the process exit code.

Example error output looks like this (may be different from the actual output):

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

## Commands that may still be unavailable

Some helper commands, such as LaTeX output, formatting, module management, or tutorial mode, may be unavailable in a particular build. When a command is not available, Litex may print a plain-text placeholder message instead of the JSON stream used for source execution.
