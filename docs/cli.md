# Litex CLI

<!-- CLI spine: choose a command family → run one typed command shape → inspect its JSON result → use the detailed family contract when needed -->

This is the complete command-line reference for the Rust `litex` binary. If
Litex is not installed yet, start with the short [setup guide](setup.md).

Created and maintained by Jiachen Shen.

Read this page online: https://litexlang.com/doc/cli

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/cli.md

> **Litex is an experimental hobby project still in beta. Expect rough edges.**

## Before You Start

To install Litex, verify the installation, or choose a package for your
platform, use the short [setup guide](setup.md). To try Litex without a local
installation, use the [online playground](https://litexlang.com).

## First Run

Start the REPL:

```bash
litex
```

The ordinary REPL is always isolated, including when the current directory
contains `litex.config`. It is a persistent terminal environment, not a
project run.

Startup output is JSON Lines. A terminal initially receives a `ready` event
and a `prompt` event:

```json
{"kind":"stream","ok":true,"stream":"repl","event":"ready","id":null,"statement_results":[],"content":{"version":"<version>","mode":"isolated"},"error":null}
{"kind":"stream","ok":true,"stream":"repl","event":"prompt","id":null,"statement_results":[],"content":">>> ","error":null}
```

Use Ctrl+D to exit. On Windows PowerShell, press Ctrl+Z and then Enter. The
REPL emits a final `closed` event before exiting.

Run a `.lit` file:

```bash
litex -f "your_file.lit"
```

If the file's direct parent contains `litex.config`, Litex loads its configured
source prefix through that file. Otherwise it runs the file in isolation. Both
forms are batch runs and exit after emitting one `run` document. Use
`litex -isolated -f "your_file.lit"` to force isolation even when a direct-parent
configuration exists.

Run Litex source directly:

```bash
litex -e "1 + 1 = 2"
```

Show the installed version:

```bash
litex -version
```

## Basic Shape

```text
litex [-strict] [-lang <code>] [-isolated] <command>
```

With no command, `litex` starts an isolated interactive verifier REPL. It does
not discover `litex.config` in the current directory or search parent
directories. This terminal is deliberately separate from the fixed module
tree, so it may load modules interactively.

The CLI has one primary command per invocation. The optional prefix has the
fixed order shown above. Options are not removed or reordered before command
parsing: repeated, out-of-order, trailing, or meaningless options are rejected.
For example:

```bash
litex -strict -isolated -f examples/tmp.lit
litex -session -f chapter.lit
litex -lang zh -e "1 = 1"
```

Every invocation must match one documented command shape exactly. Additional
tokens are rejected, except for the one documented optional graph-output path.
The parser is a hardcoded command whitelist, not a general argument parser.
For example, `litex -strict -e "1 = 1"` is valid, while
`litex -e "1 = 1" -strict`, `litex -strict -strict -e "1 = 1"`, and
`litex -strict -help` are invalid.

## Command Prefix Options

| Option | Meaning |
|--------|---------|
| `-strict` | Select a strict execution variant. Verify every configured import and every export loaded by `-f`, then reject user `trust`, `trust have`, and `axiom`. `-r` already verifies its complete export tree. It is rejected for help, version, LaTeX, extraction, and Lean commands. |
| `-lang <code>` | Localize human-readable messages and labels. JSON field names and machine discriminator values stay stable. Mathematical source strings remain in Litex syntax. |

Supported language codes are:

```text
en, zh, zh-Hans, zh-Hant, ja, ko, es, fr, de, pt, ru, ar, hi, vi, id
```

Current mappings:

| Code | Output language |
|------|-----------------|
| `en` | English |
| `zh` | Simplified Chinese |
| `zh-Hans` | Simplified Chinese |
| `zh-Hant` | Traditional Chinese |
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

Successful statement results and every `RuntimeError` use one canonical
detailed JSON projection. Detailed errors preserve causal `previous_error`
data, `failed_step`,
`failed_goal`, nested `unknown_result` data, step indexes, and internal
execution results. This includes parse, well-definedness, verification,
unknown, execution, instantiation, and inference failures. Fields for
diagnostic data that does not exist are omitted rather than synthesized.

The CLI does not have a warning branch or a top-level `warnings` field. This
contract is consistent across file, repository, REPL, session, and `try:`
execution paths.

`-compact`, `-detail`, and `-summarize` are not CLI options; using any of them
returns a `cli_error`. `-lang` affects command families that render verifier
output. `-strict` applies only to execution, graph, and session variants.
`-isolated` applies only to file, file-graph, file-session, file-conversion, and
Lean variants. Plain file selectors choose project context when their direct
parent contains `litex.config` and isolated context otherwise; `-isolated`
forces the latter. An option is rejected when its selected command has no
corresponding typed run variant.

## JSON Output Contract

Every Litex CLI response is JSON. Batch commands write one JSON document;
interactive commands write JSON Lines, with one complete JSON object per
event. Litex never prints a bare help string, version string, generated source,
graph, or handled error to stdout.

The intentionally small common envelope is:

```json
{
  "kind": "run",
  "ok": true
}
```

`kind` selects the command-family payload and `ok` reports whether that
operation succeeded. There is no `schema`, `program`, or `warnings` field.
The top-level kinds are deliberately few:

| `kind` | Commands |
|--------|----------|
| `help` | `litex -help` |
| `version` | `litex -version` |
| `run` | `litex -e`, `litex -f`, and `litex -r` |
| `artifact` | graph, LaTeX, Python, C, and Lean commands |
| `stream` | verifier REPL, LaTeX REPL, and framed session events |
| `cli_error` | unknown options, extra arguments, and unsupported combinations |

Handled errors use an `error` object. Its discriminator is also named `kind`,
not `code` or `error_type`:

```json
{
  "kind": "cli_error",
  "ok": false,
  "message": "unsupported CLI command combination"
}
```

For batch commands, exit status `0` means success, `1` means a recognized run
or artifact command failed, and `2` means the command line itself was invalid.
The JSON `ok` field is the primary machine-readable result and agrees with
these statuses. Interactive processes report individual operation failures in
their stream events and may continue running.

## Value Rules

Commands that take a value require the next command-line token to be present and
not start with `-`.

Examples:

```bash
litex -e "1 = 1"
litex -isolated -f examples/tmp.lit
litex -r examples/08_module_repository
```

This means source code beginning with `-` should usually be put in a `.lit`
file and run with `-f`.

Prefix options are parsed only in their fixed positions before the command.
A command value still cannot start with `-`; `-lang` consumes the following
language-code token in the prefix.

## Verifier Commands

| Command | Behavior |
|---------|----------|
| `litex` | Start an isolated interactive verifier REPL. |
| `litex -e <code>` | Run a Litex source string. |
| `litex -f <file>` | If the direct parent contains `litex.config`, run that module's imports plus the ordered `[export]` prefix through this registered `.lit` file; otherwise run it as an isolated script. Exit after the batch result. |
| `litex -isolated -f <file>` | Ignore any direct-parent project configuration, run one isolated batch file, and exit. |
| `litex -r <project>` | Run a module's imports, then its complete ordered `[export]` `.lit` list. |
| `litex -session -f <file>` | Select project or isolated context by the same direct-parent rule as `-f`, run the file, then keep that Runtime alive as a framed persistent session. |
| `litex -isolated -session -f <file>` | Run one standalone file, then keep that same Runtime alive as a framed persistent session. |

## Lean Compiler Commands

| Command | Behavior |
|---------|----------|
| `litex -isolated -f <input.lit> -lean <output.lean>` | Verify and compile one Litex source file into one complete Lean file. The output is replaced only after the complete source compiles successfully. |

The canonical single-file tracer can be generated through either the main CLI
or the dedicated compiler wrapper:

```bash
litex -isolated -f lean/examples/1_SetSystem.lit -lean \
  lean/examples/1_SetSystem.lean

./lean/stmt_result_to_lean_compiler.sh compile lean/examples/1_SetSystem.lit
```

Declaration-bearing `sketch` blocks compile into isolated Lean namespaces.
This preserves source order without leaking names between examples. Unsupported
or trusted routes fail closed; the compiler does not emit `sorry` or project
axioms.

Declare local project files in ordered `[export]` entries. A module
`litex.config` may declare non-standard packages in `[import]` or installed
packages in `[import std]`. Files cite canonical names such as
`Algebra::chap3::theorem` or `basics::theorem`. No `.lit` source file can
write imports; this includes standalone files selected automatically by `-f`
or forced with `-isolated -f`.

The ordinary REPL may load further interfaces dynamically with terminal
commands:

<!-- litex:skip-test -->
```text
litex> import "../Algebra" as Algebra
litex> Algebra::implementation::some_fact
litex> import std basics
litex> basics::some_fact
```

The quoted target must be a folder with a module `litex.config`. The import
runs that module's declared imports and full ordered `[export]` list.
Conceptually, each command appends a dependency to an
invisible, in-memory `litex.config` owned by that REPL. It is not written to
disk, disappears when the process exits, and never becomes a Litex statement
or statement Result. For reproducible source, declare the dependency in the
real project manifest.

For `-e`, `-f`, and `-r`, Litex emits one `run` object. The main payload is the
`statement_results` array. `target` is `eval`, `file`, or `repository`; `path`
is null for inline source and contains the requested path for file and
repository targets. `error` is null on success.

Ordinary verifier commands are designed for both inspection and automation.
Programs should read `ok`, `statement_results`, and `error`; the exit status is
also nonzero for a failed run. Ordinary `run` objects do not contain a
`summary` field.

### Run Output Examples

A successful inline run has this outer shape. Statement results contain the
detailed verifier-owned proof and execution data; the example abbreviates one
result for readability:

```json
{
  "kind": "run",
  "ok": true,
  "target": "eval",
  "path": null,
  "statement_results": [
    {
      "outcome": "success",
      "result": {
        "kind": "Fact",
        "statement": "1 + 1 = 2"
      }
    }
  ],
  "error": null
}
```

If verification fails, the successful prefix remains in `statement_results`
and `error` contains the detailed failure. The most useful error fields are
usually `kind`, `message`, `line`, `statement`, and `previous_error`:

```json
{
  "kind": "run",
  "ok": false,
  "target": "eval",
  "path": null,
  "statement_results": [],
  "error": {
    "kind": "verify_error",
    "line": 1,
    "message": "verification failed",
    "statement": "1 = 0",
    "previous_error": {
      "kind": "unknown_error",
      "line": 1,
      "message": "unknown result",
      "statement": "1 = 0",
      "failed_goal": "1 = 0"
    }
  }
}
```

Every `-f` file command is batch-only: success or failure emits one ordinary
`run` object and then exits. Use bare `litex` for the ordinary REPL, or add
`-session` when a verified file Runtime must accept later framed requests.

## Session Command

`litex -session` starts a persistent, machine-readable verifier process. With
no target, it uses the current directory's `litex.config` with the same
no-plan project startup as the ordinary REPL; `litex -isolated -session`
disables that project context.

`litex -session -f <file>` uses the same direct-parent context selection as an
ordinary `-f` command. With a configuration it runs the ordered registered
prefix; without one it runs the file in isolation. If that startup run
verifies, the process emits `ready` and accepts later blocks in the same
Runtime, so its definitions and facts are already available. If startup fails,
the process emits `startup_error` with `statement_results` and an `error`
object, then does not enter the session loop. `litex -isolated -session -f
<file>` forces the standalone branch even when configuration exists.

The session writes one JSON object per event and accepts these stdin frames:

```text
run <id> <utf8-byte-count>\n<source bytes>
artifacts <id>
close
```

`run` executes exactly one arbitrary, including multiline, source block in the
same persistent Runtime. `artifacts` returns the accumulated summary, result
graph, fact graph, and definition graph, including a successful preloaded
prefix. Every response uses the same shallow stream envelope:

```json
{"kind":"stream","ok":true,"stream":"session","event":"result","id":"example-1","statement_results":[],"content":null,"error":null}
```

The event values are `ready`, `startup_error`, `result`, `artifacts`,
`artifacts_unavailable`, `skipped`, `protocol_error`, and `closed`. Structured
verifier results are values in `statement_results` and `error`; they are not
escaped into a `trace` string.

Session `run` frames are Litex source, not terminal input. They reject
`import`, and the protocol intentionally defines no separate import frame;
dependencies for a session come from its `litex.config` preload.

A parsed top-level `try:` block always returns a `result` event with `ok: true`.
Its statement result reports whether the isolated body was `Committed` or
`RolledBack`; a rollback keeps its diagnostic but publishes no environment
changes. The client may submit another `run` frame, and `artifacts` remains
available. A malformed source frame that never parses as a `try` is an ordinary
source error. Like any other failed Litex statement, it stops later frames:
subsequent `run` requests return `skipped`, and `artifacts` returns
`artifacts_unavailable`. A `try:` nested inside another top-level statement does
not make a parse failure in that outer statement recoverable.

### Iterating after a verified file

Use `target/release/litex -session -f chap4.lit` when the selected file run
already verifies and later framed experiments should reuse that environment. A
committed outermost `try:` publishes its definitions and facts to the
persistent Runtime; a rolled-back `try:` discards only that candidate.

Session file preload always executes the selected file. It does not provide a
hidden “prefix before a failing target” mode. When repairing a failing
registered file, keep the candidate in the file and rerun release
`-f <file>` so every probe is checked in the real configured execution order.

For example, a client can send a frame shaped like:

```text
run chap5-001 <utf8-byte-count>
try:
    <one or more chap5 top-level statements>
```

The byte count covers only the source bytes after the frame header; clients
should compute it from the UTF-8 payload. Prefix execution is the cold part of
the run. File preload pays that cost once and keeps the populated Runtime;
later frames parse and verify only their submitted source.

## Graph Commands

| Command | Behavior |
|---------|----------|
| `litex -graph -e <code> <json>` | Run a source string and save one recursive statement-result/proof/FactId graph JSON object. |
| `litex -graph -f <file> <json>` | Run a file and save one recursive statement-result/proof/FactId graph JSON object. |
| `litex -graph -r <repo> <json>` | Discover the repository module graph, run its ordered `[export]` table, and save one recursive statement-result/proof/FactId graph JSON object. |
| `litex -factgraph -e <code> <json>` | Run a source string and save a fact-only verification dependency graph. |
| `litex -factgraph -f <file> <json>` | Run a file and save a fact-only verification dependency graph. |
| `litex -factgraph -r <repo> <json>` | Discover the repository module graph, run its ordered `[export]` table, and save a fact-only verification dependency graph. |
| `litex -defgraph -e <code> <json>` | Run a source string and save an environment-backed definition dependency graph. |
| `litex -defgraph -f <file> <json>` | Run a file and save an environment-backed definition dependency graph. |
| `litex -defgraph -r <repo> <json>` | Discover the repository module graph, run its ordered `[export]` table, and save an environment-backed definition dependency graph. |

The main graph is `litex-result-graph` version 3. It walks the recursive
`StmtResult` value directly and creates nodes for statement, well-definedness,
verification, proof, store, store-effect, inference, and fact layers. Tree
edges preserve result-field order; semantic citation, premise, conclusion, and
stored-fact edges use `FactId`, while memo reuse points to the exact shared
proof node. The wrapper includes a `summary`, machine-readable `nodes` and
`edges`, and a Mermaid `flowchart LR` string for quick rendering.
Its target metadata follows the runner contract: `kind` is always present and
`path` is included when a source path exists. The fact graph uses contract
version 0.2, and the definition graph uses contract version 0.3.
If the final `<json>` path is omitted, Litex returns an `artifact` object whose
`content` is the graph JSON object. If a path is supplied, Litex writes the raw
graph JSON to that file and returns an `artifact` object with `output_path` set
and `content` null. The graph is never encoded as a JSON string inside the
wrapper. In this repository, generated graph JSON, Mermaid, SVG, or PNG
artifacts should be written under `tmp/graphs/`; `tmp/` is ignored by git.

`-factgraph` is the preview proof-flow view. It deliberately omits `prop`,
function, and object-definition nodes. Its nodes are ordinary facts, `claim`s,
and `thm`s; its edges come from the verifier's actual cited facts, instantiated
`forall` facts, checked requirements, and fact-level definition unfolding. The
JSON includes a `longest_chain` field and a Mermaid flowchart. The main chain
compresses automatic inferred facts into their surrounding edges, so a reader
can follow one long, concrete chain from assumptions or trusted boundaries to a
theorem without mixing it with the definition graph.

`-defgraph` inventories definitions from the final Runtime environment and
records their dependency and provenance edges. Like the other graph commands,
it returns the graph under the artifact envelope when no output path is given.

## LaTeX Commands

| Command | Behavior |
|---------|----------|
| `litex -latex` | Start the interactive LaTeX-output REPL. |
| `litex -latex -e <code>` | Compile a source string to LaTeX. |
| `litex -latex -f <file>` | Compile a file to LaTeX. |
| `litex -latex -r <repo>` | Compile the repository ordered `[export]` table to LaTeX. |

After `-latex`, the only accepted target selectors are `-e`, `-f`, and `-r`.
If no selector follows `-latex`, Litex starts the interactive LaTeX REPL.

The LaTeX path is a compile/pretty-print path, not the same proof trace as the
verifier commands. Batch commands return an `artifact` object with
`artifact: "rendered_source"`, `format: "latex"`, and the generated text in
`content`. Failures set `ok` to false, `content` to null, and populate `error`.
The interactive LaTeX REPL emits `stream` JSON lines.

## Executable Code Extraction Commands

| Command | Behavior |
|---------|----------|
| `litex -extractpython <code>` | Verify inline source and emit Python for the supported executable definitions. |
| `litex -extractpython -f <file>` | Verify the file's ordered `# [-extract]` blocks and emit Python for the supported definitions. |
| `litex -extractpython -r <repo>` | Verify a repository's ordered `[export]` table and emit Python. |
| `litex -extractc <code>` | Verify inline source and emit a C99 translation-unit fragment for the supported executable definitions. |
| `litex -extractc -f <file>` | Verify the file's ordered `# [-extract]` blocks and emit the supported definitions as C99. |
| `litex -extractc -r <repo>` | Verify a repository's ordered `[export]` table and emit C99. |

The extraction subsystem is deliberately not a whole-Litex compiler. It emits
supported numeric assignments and `algo` definitions, reports when no
extractable definitions exist, and rejects known unsupported native-complex
and number-theory forms instead of approximating them. Python uses ordinary
floating-point expressions. C uses C99 `double`, emits no `main`, and currently
requires module-level constants to be literal arithmetic so the generated
translation unit remains valid C. Neither target proves IEEE-754 behavior.

Inline source follows the extraction flag directly; `-e` is not accepted.
The retired `-python` command is not a compatibility alias.

File extraction is explicitly selected inside the source:

```litex
# [-extract]
have fn increment(x R) R = x + 1
# [end of -extract]

# This proof is checked by an ordinary full-file run, not by extraction.
increment(1) = 2

# [-extract]
have algo for increment(x):
    x + 1
# [end of -extract]
```

Each marker must occupy a whole trimmed line. The marker lines are excluded;
the enclosed blocks are concatenated in source order and then passed to the
existing verifier and Python/C backend. The selected source must therefore be
self-contained. `-f` does not load a configured project prefix or verify the
unselected statements. It preserves blank lines internally so diagnostics
still point to the original file locations. Missing, nested, unmatched, or
unclosed markers are errors; there is no whole-file fallback. Use ordinary
`litex -f <file>` to verify the complete mathematical development. Inline and
`-r` extraction retain their whole-input behavior.

Extraction returns an `artifact` object with `artifact: "extracted_code"`,
`format: "python"` or `"c"`, and the generated source in `content`. The Lean
compiler similarly returns `artifact: "compiled_source"`, `format: "lean"`,
and its written file in `output_path`.

## Information Commands

| Command | Behavior |
|---------|----------|
| `litex -help` | Return `{"kind":"help","ok":true,"entries":[...]}` and exit. |
| `litex -version` | Return `{"kind":"version","ok":true,"version":"..."}` and exit. |

Unknown commands return one `cli_error` object and exit with code `2`. They do
not append help text. For example, `litex -j` returns:

```json
{
  "kind": "cli_error",
  "ok": false,
  "message": "unsupported CLI command combination"
}
```

## Project Modules

> **new_pipeline design target:** no `submodule` and no `[hierarchy]`;
> `[export]` is `.lit` files only; `[import]` / `[import std]` both mount
> modules under one shared alias namespace (`[import std]` bare `N` means
> `N = N`; `Alias = StdName` resolves to `<std_root>/<StdName>`). Canonical
> write-up:
> [`src/new_pipeline/module_manager/README.md`](../src/new_pipeline/module_manager/README.md).
> Legacy runners may still accept older manifests until migration finishes.

Use `litex.config` to organize a module:

- select each participating `.lit` file exactly once, in mathematical order,
  under `[export]` (files only; no child-folder export);
- declare external module folders under `[import] Alias = path` and std
  packages under `[import std]` as either bare `N` (meaning `N = N`) or
  `Alias = StdName` (path `<std_root>/<StdName>`);
- keep import aliases unique across both import sections;
- cite mounted packages and exports with canonical names, such as
  `Algebra::chap1::name` or `basics::name`.

`[export]` is an explicit selection list, not an inventory of the directory.
Unlisted files and folders are sidecars: module discovery does not parse them,
execute them, or add them to the module namespace. Declared export paths still
must exist and point to a `.lit` file. Imported targets must be external
module folders; imports cannot target individual `.lit` files.

`-r` and `-f` share one left-to-right order inside a module: run imports, then
run the ordered `[export]` `.lit` list. Running a module runs that full list.
Running a registered file follows the same prefix and stops after that file.
When the direct parent has no `litex.config`, `litex -f` instead performs one
isolated batch run. It does not search ancestor folders. A present but invalid
configuration, or a target that is not exported exactly once, remains a
project error and never falls back. Use `litex -isolated -f` to force isolation
when configuration is present. `new_pipeline` does not wire project `-r` /
`-f` mount yet.

Dependency order is the module's `[export]` order after its imports.
Source-level `import` is rejected everywhere; project source uses its
manifest, while only an interactive terminal recognizes import commands.

Each `[import]` declaration creates a private module instance. Two aliases of
one physical folder remain distinct, and imports internal to an imported module
do not become public to its importer.

`litex -r <project>` verifies the complete ordered `[export]` list. In contrast,
`litex -f <file>` trusts and loads only the earlier `[export]` entries needed to
provide that file's project context, then verifies the selected file. Litex
reports those prefix entries as `unverified_imports`. `[import]` and `[import std]`
are also trusted by default; rerun with `-strict` to verify every loaded
dependency. Do not write `trust` in `litex.config`: remove that prefix when
migrating an older project.

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

Run a standalone file:

```bash
litex -f examples/tmp.lit
```

Run a project plan:

```bash
litex -r examples/08_module_repository
```

Run a strict CI-style check:

```bash
litex -strict -f examples/tmp.lit
```

Generate a recursive result graph:

```bash
litex -graph -f examples/04_case_studies/gcd_from_finite_divisors.lit tmp/graphs/gcd_graph.json
```

Generate a fact-only verification chain:

```bash
litex -isolated -factgraph -f examples/tmp.lit tmp/graphs/tmp_fact_graph.json
```

Run with Chinese output labels:

```bash
litex -lang zh -e "1 = 1"
```

Compile a file to LaTeX:

```bash
litex -isolated -latex -f examples/tmp.lit
```
