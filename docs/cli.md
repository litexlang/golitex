# Litex CLI

This page records the command-line rules implemented by the Rust `litex`
binary.

## Basic Shape

```text
litex [global options] [command]
```

With no command, `litex` starts the interactive verifier REPL.

The CLI has one primary command per invocation. Global options are removed
before the primary command is parsed, so they may appear before or after the
primary command. Prefer putting them before the command for readability:

```bash
litex -detail -strict -f examples/tmp.lit
litex -summarize -f examples/tmp.lit
litex -lang zh -runner -e "1 = 1"
```

Do not rely on extra positional tokens after a command's required values, except
for the documented graph-output path after `litex -graph`. The current parser
is command-oriented, not a general argument parser.

## Global Options

| Option | Meaning |
|--------|---------|
| `-detail` | Include fuller JSON trace details. For runner output, this also keeps raw file paths instead of replacing file targets with `entry`. |
| `-strict` | Reject user `proof_debt`, `suppose`, and `axiom` statements after builtin initialization. This is useful for CI or benchmark runs where unsafe assumptions should fail. |
| `-summarize` | Append one final run-summary JSON object after ordinary verifier command output. |
| `-lang <code>` | Localize JSON keys and explanatory labels. Mathematical source strings inside fields such as `statement`, `fact`, and `cited_statement` stay in Litex syntax. |

Supported language codes are:

```text
en, zh, zh-Hans, ja, ko, es, fr, de, pt, ru, ar, hi, vi, id
```

Current mappings:

| Code | Output language |
|------|-----------------|
| `en` | English |
| `zh` | Simplified Chinese |
| `zh-Hans` | Traditional Chinese |
| `ja` | Japanese |
| `ko` | Korean |
| `es` | Spanish |
| `fr` | French |
| `de` | German |
| `pt` | Portuguese |
| `ru` | Russian |
| `ar` | Arabic |
| `hi` | Hindi |
| `vi` | Vietnamese |
| `id` | Indonesian |

`-detail`, `-strict`, and `-lang` mainly affect verifier, runner, and graph commands.
`-summarize` affects ordinary verifier commands.
They do not make module-management or tutorial placeholder commands functional.

## Value Rules

Commands that take a value require the next command-line token to be present and
not start with `-`.

Examples:

```bash
litex -e "1 = 1"
litex -f examples/tmp.lit
litex -r examples
```

This means source code beginning with `-` should usually be put in a `.lit`
file and run with `-f`.

Because `-detail`, `-strict`, and `-summarize` are removed globally before
command parsing, do not use a standalone command value exactly equal to any of
those flags. `-lang` also consumes the next token globally.

## Verifier Commands

| Command | Behavior |
|---------|----------|
| `litex` | Start the interactive verifier REPL. |
| `litex -e <code>` | Run a Litex source string. |
| `litex -f <file>` | Run one Litex file as an isolated script. It does not read `mod.lit`; `export` and `local_import` are unavailable. |
| `litex -r <repo>` | Discover and validate `<repo>/mod.lit` recursively, then run `<repo>/main.lit`. |

For `-e`, `-f`, and `-r`, Litex prints statement-by-statement JSON output. A
successful run prints one success object per statement. A failed run prints the
successful prefix followed by an error object.

With `-summarize`, Litex appends one final JSON object whose `output_type` is
`"run summary"`. The ordinary statement output before that object is unchanged.
The summary reports top-level and expanded statement counts, fact/prop/theorem
definition counts, proof-block and `by` counts, direct `proof_debt` statements,
indirect proof-debt dependencies, axioms, supposes, abstract interfaces, and
stack/runner warnings. It also includes `statement_type_counts`,
`output_type_counts`, and a `statements` array with line numbers and rendered
statement text for editor-side cursor selection. Prefer:

```bash
litex -summarize -f examples/tmp.lit
```

Ordinary verifier commands are designed for interactive inspection. Programs
should read the JSON result instead of relying only on the process exit code.
Use `-runner` when a script or CI job needs a wrapper object and a nonzero exit
code on verification failure.

## Runner Commands

| Command | Behavior |
|---------|----------|
| `litex -runner -e <code>` | Run a source string and return one wrapper JSON object. |
| `litex -runner -f <file>` | Run a file and return one wrapper JSON object. |
| `litex -runner -r <repo>` | Discover the repository module graph, run `<repo>/main.lit`, and return one wrapper JSON object. |

The runner wrapper contains:

| Field | Meaning |
|-------|---------|
| `runner` | Runner name, currently `litex-runner`. |
| `runner_version` | Runner output-contract version. |
| `result` | `success` or `error` for the whole run. |
| `ok` | Boolean success flag. |
| `target` | Target kind and label. Without `-detail`, file and repo labels are hidden as `entry`. |
| `error` | Target-load error object, or `null` when the target was loaded. |
| `trace` | The ordinary statement-by-statement Litex JSON output as a string. |

Runner exit behavior:

- exits with code `0` when `ok` is true;
- exits with code `1` when the checked run fails or the target cannot be loaded;
- exits with code `2` for CLI usage errors, such as a missing value.

## Graph Commands

| Command | Behavior |
|---------|----------|
| `litex -graph -e <code> <json>` | Run a source string and save one prop/function/fact relation graph JSON object. |
| `litex -graph -f <file> <json>` | Run a file and save one prop/function/fact relation graph JSON object. |
| `litex -graph -r <repo> <json>` | Discover the repository module graph, run `<repo>/main.lit`, and save one prop/function/fact relation graph JSON object. |

The graph is an MVP concept map for direct Litex vocabulary references. It
creates nodes for `prop`, `have fn`, and facts such as `thm`, `axiom`, and
`claim`. Edges point from the referenced dependency to the later consumer:
`uses_prop`, `uses_fn`, and `justified_by` for theorem-backed function
construction. The wrapper includes a `summary`, machine-readable `nodes` and
`edges`, a sorted `usage` table, and a Mermaid `flowchart LR` string for quick
rendering. Nodes include `uses_count` and `used_by_count`; edges include
`count`, so UI code can rank often-cited props, functions, facts, and theorems.
If the final `<json>` path is omitted, Litex prints the graph JSON to stdout for
quick debugging. In this repository, generated graph JSON, Mermaid, SVG, or PNG
artifacts should be written under `tmp/graphs/`; `tmp/` is ignored by git.

## LaTeX Commands

| Command | Behavior |
|---------|----------|
| `litex -latex` | Start the interactive LaTeX-output REPL. |
| `litex -latex -e <code>` | Compile a source string to LaTeX. |
| `litex -latex -f <file>` | Compile a file to LaTeX. |
| `litex -latex -r <repo>` | Compile `<repo>/main.lit` to LaTeX. |

After `-latex`, the only accepted target selectors are `-e`, `-f`, and `-r`.
If no selector follows `-latex`, Litex starts the interactive LaTeX REPL.

The LaTeX path is a compile/pretty-print path, not the same JSON proof trace as
the verifier commands. If LaTeX compilation hits a Litex error, the CLI prints a
JSON error object.

## Information Commands

| Command | Behavior |
|---------|----------|
| `litex -help` | Print help and exit. |
| `litex -version` | Print the installed Litex kernel version and exit. |
| `litex -upgrade` | Print platform-specific upgrade instructions and exit. |

Unknown commands print an error and the help message, then exit with code `2`.

## Reserved Helper Commands

These commands are parsed by the Rust CLI but are not implemented as functional
features in the Rust kernel yet:

| Command | Current status |
|---------|----------------|
| `litex -fmt <code>` | Prints a placeholder message. |
| `litex -install <module>` | Reserved for module management; not implemented in the Rust kernel yet. |
| `litex -uninstall <module>` | Reserved for module management; not implemented in the Rust kernel yet. |
| `litex -list` | Reserved for module management; not implemented in the Rust kernel yet. |
| `litex -update <module>` | Reserved for module management; not implemented in the Rust kernel yet. |
| `litex -tutorial` | Reserved for tutorial mode; not implemented in the Rust kernel yet. |

Use source files, imports, and `-f` or `-r` for current local workflows.

## Practical Recipes

Run a one-line fact:

```bash
litex -e "1 = 1"
```

Run a file with fuller output:

```bash
litex -detail -f examples/tmp.lit
```

Run a repository entry file:

```bash
litex -r examples
```

Run a strict CI-style check:

```bash
litex -strict -runner -f examples/tmp.lit
```

Generate a relation graph:

```bash
litex -graph -f scripts/analysis-one/chapters_in_litex/chap6.lit tmp/graphs/chap6_graph.json
```

Run with Chinese output labels:

```bash
litex -lang zh -runner -e "1 = 1"
```

Compile a file to LaTeX:

```bash
litex -latex -f examples/tmp.lit
```
