# Litex CLI

This page records the command-line rules implemented by the Rust `litex`
binary.

## Basic Shape

```text
litex [global options] [command]
```

With no command, `litex` starts an isolated interactive verifier REPL. It does
not discover `litex.config` in the current directory or search parent
directories. This terminal is deliberately separate from the fixed module
tree, so it may load modules interactively.

The CLI has one primary command per invocation. Global options are removed
before the primary command is parsed, so they may appear before or after the
primary command. Prefer putting them before the command for readability:

```bash
litex -detail -strict -f examples/tmp.lit
litex -summarize -f examples/tmp.lit
litex -lang zh -runner -e "1 = 1"
```

Do not rely on extra positional tokens after a command's required values, except
for the documented graph-output path after `litex -graph` or `litex
-factgraph`. The current parser is command-oriented, not a general argument
parser.

## Global Options

| Option | Meaning |
|--------|---------|
| `-compact` | Show only `result`, `type`, `line`, and `statement` for each execution result. |
| *(no output flag)* | Use the normal reading view: internal statements plus assumptions, conclusions, and direct `why_verified` reasons, without audit duplication. |
| `-detail` | Include fuller JSON trace details, including well-definedness, verification, and environment phases. For runner output, this also keeps raw file paths instead of replacing file targets with `entry`. |
| `-strict` | Reject user `trust`, `trust have`, and `axiom`. Configured imports still load normally. This is useful for CI or benchmark runs where user-introduced unsafe assumptions should fail. |
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
| `litex` | Start an isolated interactive verifier REPL. |
| `litex -isolated` | Compatibility spelling for the same isolated interactive REPL. |
| `litex -e <code>` | Run a Litex source string. |
| `litex -f <file>` | If the direct parent has `litex.config`, trace to its module and run the recursive `[export]` prefix through this file. Otherwise run the file, then continue in an isolated REPL with that file's environment. |
| `litex -isolated -f <file>` | Force one Litex file to run as an isolated script. |
| `litex -r <project>` | Run a module's complete recursive `[export]` tree, or trace to the module and run the prefix through a selected submodule's complete subtree. |

Declare local project files and child submodules in recursive ordered
`[export]` entries. Only a `[hierarchy] module` declares non-standard packages
in `[import]` or installed packages in `[import std]`. Files cite canonical
names such as `Part2::chap3::theorem` or
`std::basics::implementation::theorem`. Module source files cannot write
source-level imports.

The ordinary REPL, and the continued terminal after a successful isolated
`-f`, may load further interfaces dynamically:

<!-- litex:skip-test -->
```litex
import "../Algebra" as Algebra
Algebra::implementation::some_fact

import std basics
std::basics::implementation::some_fact
```

The quoted target must be a folder whose `litex.config` declares
`[hierarchy] module`. The import runs that module's declared imports and full
ordered `[export]` tree. The terminal keeps the resulting environment, but the
imported module's own source files remain non-isolated and therefore cannot
write dynamic `import` statements.

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
| `litex -runner -r <repo>` | Discover the repository module graph, run its ordered `[export]` table, and return one wrapper JSON object. |

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
same persistent Runtime. `artifacts` returns the accumulated summary, relation
graph, and fact graph after successful blocks. The event values are `ready`,
`block`, `artifacts`,
`skipped`, and `protocol_error`; textual verifier output is returned in the
JSON-string `trace` field so a client never has to parse terminal prompts.

## Graph Commands

| Command | Behavior |
|---------|----------|
| `litex -graph -e <code> <json>` | Run a source string and save one prop/function/fact relation graph JSON object. |
| `litex -graph -f <file> <json>` | Run a file and save one prop/function/fact relation graph JSON object. |
| `litex -graph -r <repo> <json>` | Discover the repository module graph, run its ordered `[export]` table, and save one prop/function/fact relation graph JSON object. |
| `litex -factgraph -e <code> <json>` | Run a source string and save a fact-only verification dependency graph. |
| `litex -factgraph -f <file> <json>` | Run a file and save a fact-only verification dependency graph. |
| `litex -factgraph -r <repo> <json>` | Discover the repository module graph, run its ordered `[export]` table, and save a fact-only verification dependency graph. |

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

`-factgraph` is the preview proof-flow view. It deliberately omits `prop`,
function, and object-definition nodes. Its nodes are ordinary facts, `claim`s,
and `thm`s; its edges come from the verifier's actual cited facts, instantiated
`forall` facts, checked requirements, and fact-level definition unfolding. The
JSON includes a `longest_chain` field and a Mermaid flowchart. The main chain
compresses automatic inferred facts into their surrounding edges, so a reader
can follow one long, concrete chain from assumptions or trusted boundaries to a
theorem without mixing it with the definition graph.

## LaTeX Commands

| Command | Behavior |
|---------|----------|
| `litex -latex` | Start the interactive LaTeX-output REPL. |
| `litex -latex -e <code>` | Compile a source string to LaTeX. |
| `litex -latex -f <file>` | Compile a file to LaTeX. |
| `litex -latex -r <repo>` | Compile the repository ordered `[export]` table to LaTeX. |

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

Use `litex.config` to organize a folder tree:

- put `module` under `[hierarchy]` at an independently runnable/importable root;
- put `submodule` under `[hierarchy]` in every exported child folder;
- list every direct child file and folder exactly once, in mathematical order,
  under `[export]`;
- declare external module folders under `[import]` and installed packages under
  `[import std]`, only in the top-level module;
- cite earlier entries with their full folder/file aliases, such as
  `Part2::chap7::name` or `std::basics::implementation::name`.

A configured folder may contain only `litex.config` and the direct children
listed in `[export]`. Exported folders must be submodules. Imported targets must
be external module folders; imports cannot target files, submodules, or
descendants of the importing module.

`-r` and `-f` share one recursive left-to-right order. Running a top-level
module runs the whole tree. Running a submodule traces back to its module,
executes every preceding entry, then executes the selected submodule in full.
Running a registered file follows the same prefix and stops after that file. A
file whose direct parent has no `litex.config` runs in isolation.

There is no `[requires]`, `[run]`, or flatten mode. Every folder and file alias
stays in the canonical namespace. Source-level `import` is reserved for the
isolated terminal; module source uses its manifest instead.

Each `[import]` declaration creates a private module instance. Two aliases of
one physical folder remain distinct, and imports internal to an imported module
do not become public to its importer.

For an explicitly trusted project entry, write
`trust chap7 = "./chap7.lit"` in `[export]`. Ordinary runs skip its proof
processing but preserve direct environment effects; `-strict` verifies it
normally. For a trusted non-standard package, use the same `trust` prefix in
`[import]`. Standard package declarations have no trust modifier.

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

Generate a fact-only verification chain:

```bash
litex -factgraph -f examples/tmp.lit tmp/graphs/tmp_fact_graph.json
```

Run with Chinese output labels:

```bash
litex -lang zh -runner -e "1 = 1"
```

Compile a file to LaTeX:

```bash
litex -latex -f examples/tmp.lit
```
