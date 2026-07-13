# Litex CLI

This page records the command-line rules implemented by the Rust `litex`
binary.

## Basic Shape

```text
litex [global options] [command]
```

With no command, `litex` starts the interactive verifier REPL. If the current
directory directly contains `litex.config`, it discovers that project without
running its `[run]` plan. The persistent REPL environment can then load any
root `[export]` on demand with `local import name`. Use `litex -isolated` to
force the ordinary isolated REPL. Litex does not search parent directories for
a project configuration.

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
| `-compact` | Show only `result`, `type`, `line`, and `statement` for each execution result. |
| *(no output flag)* | Use the normal reading view: internal statements plus assumptions, conclusions, and direct `why_verified` reasons, without audit duplication. |
| `-detail` | Include fuller JSON trace details, including well-definedness, verification, and environment phases. For runner output, this also keeps raw file paths instead of replacing file targets with `entry`. |
| `-strict` | Reject user `trust`, `trust have`, and `axiom` statements after builtin initialization. This is useful for CI or benchmark runs where unsafe assumptions should fail. |
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

`-compact` affects ordinary verifier commands. `-detail`, `-strict`, and `-lang` mainly affect verifier, runner, and graph commands.
`-summarize` affects ordinary verifier commands.
They do not make module-management or tutorial placeholder commands functional.

## Value Rules

Commands that take a value require the next command-line token to be present and
not start with `-`.

Examples:

```bash
litex -e "1 = 1"
litex -f examples/tmp.lit
litex -r examples/08_module_repository
```

This means source code beginning with `-` should usually be put in a `.lit`
file and run with `-f`.

Because `-compact`, `-detail`, `-strict`, and `-summarize` are removed globally before
command parsing, do not use a standalone command value exactly equal to any of
those flags. `-lang` also consumes the next token globally.

## Verifier Commands

| Command | Behavior |
|---------|----------|
| `litex` | Start the interactive verifier REPL; use the current directory's `litex.config` when present, without running its `[run]` plan. |
| `litex -isolated` | Start an isolated interactive REPL, ignoring the current directory's project configuration. |
| `litex -e <code>` | Run a Litex source string. |
| `litex -f <file>` | Run a file in its outermost registering `litex.config` project when one exists; otherwise run it as an isolated script. |
| `litex -isolated -f <file>` | Force one Litex file to run as an isolated script. |
| `litex -r <project>` | Discover and validate `<project>/litex.config` recursively, then run its ordered `[run]` plan. |

Declare project files and child modules in `[export]` in `litex.config`,
then bind them with `local import`; ordinary `import Name` names a declared
root module.

For `-e`, `-f`, and `-r`, Litex prints statement-by-statement JSON output. A
successful run prints one success object per statement. A failed run prints the
successful prefix followed by an error object.

With `-summarize`, Litex appends one final JSON object whose `output_type` is
`"run summary"`. The ordinary statement output before that object is unchanged.
The summary reports top-level and expanded statement counts, fact/prop/theorem
definition counts, proof-block and `by` counts, direct `trust` statements,
indirect trusted dependencies, axioms, trusted local names, abstract interfaces, and
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
| `litex -runner -r <repo>` | Discover the repository module graph, run its `[run]` plan, and return one wrapper JSON object. |

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

## Session Command

`litex -session` starts a persistent, machine-readable verifier process. It
uses the current directory's `litex.config` with the same no-plan project
startup as the ordinary REPL; `litex -isolated -session` disables that project
context. It writes one JSON object per event and accepts these stdin frames:

```text
run <id> <utf8-byte-count>\n<source bytes>
artifacts <id>
close
```

`run` executes exactly one arbitrary, including multiline, source block in the
same persistent Runtime. `artifacts` returns the accumulated summary and graph
after successful blocks. The event values are `ready`, `block`, `artifacts`,
`skipped`, and `protocol_error`; textual verifier output is returned in the
JSON-string `trace` field so a client never has to parse terminal prompts.

## Graph Commands

| Command | Behavior |
|---------|----------|
| `litex -graph -e <code> <json>` | Run a source string and save one prop/function/fact relation graph JSON object. |
| `litex -graph -f <file> <json>` | Run a file and save one prop/function/fact relation graph JSON object. |
| `litex -graph -r <repo> <json>` | Discover the repository module graph, run its `[run]` plan, and save one prop/function/fact relation graph JSON object. |

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
| `litex -latex -r <repo>` | Compile the repository `[run]` plan to LaTeX. |

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

## Project Modules

Use `litex.config` to organize a multi-file project:

- list ordered bare paths in `[run]`, for example `./chap7.lit` or `./Algebra`;
- declare every run target, files, and child modules in `[export]`, for example `chap7 = "./chap7.lit"`;
- use `local import name` inside registered sources;
- run the project plan with `litex -r <project>` or one registered chapter with `litex -f <file>`.

Ordinary `import Name` loads a declared root module.

For an explicitly trusted project dependency, write `trust import Name` or
`trust local import name` in a registered `.lit` source. Litex still resolves
the declared project target, reads it, parses it, and checks dependency cycles,
but skips its well-definedness and proof processing and keeps only its
environment effects. Trusted imports are rejected by `-strict`; their presence
is recorded as a `trust_import` or `trust_local_import` dependency in the run.

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

Run a project plan:

```bash
litex -r examples/08_module_repository
```

Run a strict CI-style check:

```bash
litex -strict -runner -f examples/tmp.lit
```

Generate a relation graph:

```bash
litex -graph -f textbooks/Analysis/chapter06-sequential-limits.lit tmp/graphs/chapter06_graph.json
```

Run with Chinese output labels:

```bash
litex -lang zh -runner -e "1 = 1"
```

Compile a file to LaTeX:

```bash
litex -latex -f examples/tmp.lit
```
