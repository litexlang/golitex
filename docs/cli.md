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
litex -detail -strict -isolated -f examples/tmp.lit
litex -summarize -isolated -f examples/tmp.lit
litex -compact -f chapter.lit -trust-before-line 420
litex -lang zh -runner -e "1 = 1"
```

Do not rely on extra positional tokens after a command's required values, except
for the documented graph-output path after `litex -graph` or `litex
-factgraph`. The current parser is command-oriented, not a general argument
parser.

## Global Options

| Option | Meaning |
|--------|---------|
| `-compact` | Show only `result`, `type`, `line`, and `statement` for successful execution results. Any `RuntimeError` is always detailed. |
| *(no output flag)* | Use the normal reading view for successful results: internal statements plus assumptions, conclusions, and direct `why_verified` reasons, without audit duplication. Any `RuntimeError` is always detailed. |
| `-detail` | Include fuller JSON trace details for both successful results and errors, including well-definedness, verification, and environment phases. For runner output, this also keeps raw file paths instead of replacing file targets with `entry`. |
| `-strict` | Verify every configured import and every export loaded by `-f`, then reject user `trust`, `trust have`, and `axiom`. `-r` already verifies its complete export tree. Use it for CI or a complete dependency audit. |
| `-trust-before-line <X>` | Preview development option for a direct `-f` or `-isolated -f` run. Trust top-level statements whose header is before line `X`, then verify normally from the statement whose header is exactly line `X`. |
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

Output style controls successful statement results. Every `RuntimeError` is
rendered with the detailed error projection, whether the command uses
`-compact`, the normal view, or `-detail`. Detailed errors preserve available
`phases`, causal `previous_error` data, `failed_step`, `failed_goal`, nested
`unknown_result` data, step indexes, and internal execution results. This
includes parse, well-definedness, verification, unknown, execution,
instantiation, and inference failures. Fields for diagnostic data that does
not exist are omitted rather than synthesized.

Only the failing result is upgraded. Earlier successful statements retain the
selected output style, and warning-only successful results are not
automatically expanded. This contract is consistent across file, repository,
REPL, runner, session, and `try:` execution paths. Existing error fields and
exit-code behavior are unchanged; compact and normal failures may contain
additional diagnostic fields.

`-compact` affects ordinary verifier commands. `-detail`, `-strict`, and `-lang` mainly affect verifier, runner, and graph commands.
`-summarize` affects ordinary verifier commands.
They do not make module-management or tutorial placeholder commands functional.

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

Because `-compact`, `-detail`, `-strict`, and `-summarize` are removed globally before
command parsing, do not use a standalone command value exactly equal to any of
those flags. `-lang` also consumes the next token globally.

`-trust-before-line` consumes a positive ASCII decimal line number globally,
so it may appear before or after `-f`. It may appear only once.

## Verifier Commands

| Command | Behavior |
|---------|----------|
| `litex` | Start an isolated interactive verifier REPL. |
| `litex -isolated` | Compatibility spelling for the same isolated interactive REPL. |
| `litex -e <code>` | Run a Litex source string. |
| `litex -f <file>` | Require `litex.config` in the direct parent, trace to the module root, and run the recursive `[export]` prefix through this file. It fails if that direct configuration is absent. |
| `litex -isolated -f <file>` | Run one Litex file as an isolated script, without project discovery; a successful ordinary CLI run then continues in an isolated REPL. |
| `litex -r <project>` | Run a module's complete recursive `[export]` tree, or trace to the module and run the prefix through a selected submodule's complete subtree. |
| `litex -session -f <file>` | Run the registered project prefix through one file, then keep that same Runtime alive as a framed persistent session. |
| `litex -session -before <file>` | Run the registered project prefix before one file, exclude that file, and start the persistent session in its file environment. |

### Trusted prefix file checks (preview)

When editing the latter part of a long file, use:

```bash
litex -compact -f chapter.lit -trust-before-line 420
```

Line `X` must be the physical, one-based line of an exact top-level statement
header in the target file. A comment, blank line, nested proof line, line
inside a multiline statement, or an end-of-file sentinel is rejected before
any statement runs. Litex does not move the boundary to the next statement.

Every top-level statement whose header is before `X` is parsed and applied to
the environment in trusted mode. Names, definitions, facts, and inferred facts
remain available to the suffix, and syntax or duplicate-name errors still
fail. Litex skips only well-definedness and proof verification for those
statements. The statement beginning exactly at `X` and every later top-level
statement are verified normally.

The cutoff applies only to the file named by the direct `-f`. Configured
imports and earlier exports keep their ordinary execution policy. It is not
supported by `-r`, `-e`, `-session`, `-runner`, graph output, Python, or LaTeX,
and it cannot be combined with `-strict` or extra positional arguments.

A cutoff run emits a leading `trusted_prefix` boundary record and always ends
with one run summary, even without `-summarize`. Statement objects retain their
normal `type` and report `verification_status`: prefix statements report
`trusted_prefix`, while suffix statements report `verified`. The runtime does
not attach transitive trust metadata to suffix statements that use prefix
facts. The run is still not fully checkable because the prefix proofs were
skipped. `-compact` retains the statement status needed to see that boundary.
An `-isolated -f` cutoff run exits after this summary instead of continuing
into the interactive REPL.

Declare local project files and child submodules in recursive ordered
`[export]` entries. Only a `[hierarchy] module` declares non-standard packages
in `[import]` or installed packages in `[import std]`. Files cite canonical
names such as `Part2::chap3::theorem` or
`basics::theorem`. Module source files cannot write
source-level imports.

The ordinary REPL, and the continued terminal after a successful isolated
`-f`, may load further interfaces dynamically:

<!-- litex:skip-test -->
```litex
import "../Algebra" as Algebra
Algebra::implementation::some_fact

import std basics
basics::some_fact
```

The quoted target must be a folder whose `litex.config` declares
`[hierarchy] module`. The import runs that module's declared imports and full
ordered `[export]` tree. The terminal keeps the resulting environment, but the
imported module's own source files remain non-isolated and therefore cannot
write dynamic `import` statements.

For `-e`, `-f`, and `-r`, Litex prints statement-by-statement JSON output. A
successful run prints one success object per statement. A failed run prints the
successful prefix in the selected success style followed by a detailed error
object.

With `-summarize`, Litex appends one final JSON object whose `output_type` is
`"run summary"`. The ordinary statement output before that object is unchanged.
The summary reports top-level and expanded statement counts, fact/prop/theorem
definition counts, proof-block and `by` counts, direct `trust` statements,
`trust have` assumptions, axioms, abstract interfaces, and stack/runner
warnings. These are direct statement counts; the runtime does not classify
theorems or derived facts by transitive trust dependency. It also includes
`statement_type_counts`, `output_type_counts`, and a `statements` array with
line numbers and rendered statement text for editor-side cursor selection.
Prefer:

```bash
litex -summarize -isolated -f examples/tmp.lit
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

`litex -session` starts a persistent, machine-readable verifier process. With
no target, it uses the current directory's `litex.config` with the same
no-plan project startup as the ordinary REPL; `litex -isolated -session`
disables that project context.

`litex -session -f <file>` first runs the same ordered project prefix as an
ordinary registered-file `-f` command. If the prefix verifies, the process
emits `ready` and accepts later blocks in the same Runtime, so definitions and
facts from the prefix are already available. If the prefix fails, the process
emits `startup_error` with the verifier trace and does not enter the session
loop. `litex -isolated -session -f <file>` provides the analogous behavior for
an intentionally standalone file.

`litex -session -before <file>` discovers the file in its direct-parent
`litex.config`, loads imports and recursive ordered exports strictly before the
target, and does not execute the target or anything after it. The session then
executes submitted blocks in the target's own file environment, so names and
module references match the eventual source file. This mode is intended for a
new, incomplete, or currently failing file. It cannot be combined with
`-isolated` because its ordering and file environment come from the project
configuration.

The session writes one JSON object per event and accepts these stdin frames:

```text
run <id> <utf8-byte-count>\n<source bytes>
artifacts <id>
close
```

`run` executes exactly one arbitrary, including multiline, source block in the
same persistent Runtime. `artifacts` returns the accumulated summary, relation
graph, and fact graph, including a successful preloaded prefix. The event
values are `ready`, `startup_error`, `block`, `artifacts`, `skipped`, and
`protocol_error`; textual verifier output is returned in the JSON-string
`trace` field so a client never has to parse terminal prompts.

A failed top-level `try:` block returns a `block` event with `ok: false`, but
does not stop the session because `try:` has already discarded its temporary
environment. The client may submit another `run` frame, and `artifacts` remains
available. Any other failed Litex statement stops execution of later frames:
subsequent `run` requests return `skipped`, and `artifacts` returns
`artifacts_unavailable`. A `try:` nested inside another top-level statement does
not make that outer statement recoverable.

### Repairing the next project file

Suppose `chap5.lit` follows `chap4.lit` in the module's ordered `[export]`
table. The same loop applies whether chap5 is empty, incomplete, or currently
failing.

1. Start
   `target/release/litex -compact -session -before chap5.lit`. This loads the
   configured prefix through chap4, excludes chap5, and enters chap5's file
   environment.
2. After the `ready` event, send the top-level statements from `chap5.lit` in
   source order. Wrap every candidate frame in a literal outermost `try:`.
3. A successful `try:` commits its declarations and facts to the persistent
   Runtime. A failed `try:` discards only that candidate, so the chap1--chap4
   prefix and all earlier successful chap5 frames remain available.
4. Correct and resend only the failed fragment. If a proof remains blocked,
   keep its intended statement and use the narrowest explicit `trust` before
   continuing with the next statement.
5. Write each accepted statement back to `chap5.lit`. When all fragments have
   been replayed, run release `-f chap5.lit` once as the clean file checkpoint.

A failed `try:` never requires a restart. Restart from `-before chap5.lit` only
if the process exits, a loaded predecessor changes, or an already committed
declaration must be replaced under the same name.

For example, a client can send a frame shaped like:

```text
run chap5-001 <utf8-byte-count>
try:
    <one or more chap5 top-level statements>
```

The byte count covers only the source bytes after the frame header; clients
should compute it from the UTF-8 payload. Prefix execution is the cold part of
the run. `-session -before` pays that cost once and keeps the populated target
file Runtime; later frames parse and verify only their submitted source.
`-compact` reduces rendered output but does not replace release optimization or
Runtime reuse.

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
- cite earlier entries with their canonical export path, such as
  `Part2::chap7::name` or `basics::name`.

A configured folder may contain only `litex.config` and the direct children
listed in `[export]`. Exported folders must be submodules. Imported targets must
be external module folders; imports cannot target files, submodules, or
descendants of the importing module.

`-r` and `-f` share one recursive left-to-right order. Running a top-level
module runs the whole tree. Running a submodule traces back to its module,
executes every preceding entry, then executes the selected submodule in full.
Running a registered file follows the same prefix and stops after that file.
`litex -f` requires the file's direct parent to have `litex.config`; use
`litex -isolated -f` for a standalone file.

Dependency order is the recursive `[export]` order. A `module` with exactly
one `.lit` export may write `[module]` then `flatten = true`; its public
interface omits that export-name segment. `std/basics` uses this form, so `[import std] basics` exposes
`basics::name`. Source-level `import` is reserved for isolated runtimes; module
source uses its manifest instead.

Each `[import]` declaration creates a private module instance. Two aliases of
one physical folder remain distinct, and imports internal to an imported module
do not become public to its importer.

`litex -r <project>` verifies the complete ordered `[export]` tree. In contrast,
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

Run a file with fuller output:

```bash
litex -detail -isolated -f examples/tmp.lit
```

Run a project plan:

```bash
litex -r examples/08_module_repository
```

Run a strict CI-style check:

```bash
litex -strict -runner -isolated -f examples/tmp.lit
```

Generate a relation graph:

```bash
litex -graph -f textbooks/Analysis/chapter06-sequential-limits.lit tmp/graphs/chapter06_graph.json
```

Generate a fact-only verification chain:

```bash
litex -factgraph -isolated -f examples/tmp.lit tmp/graphs/tmp_fact_graph.json
```

Run with Chinese output labels:

```bash
litex -lang zh -runner -e "1 = 1"
```

Compile a file to LaTeX:

```bash
litex -latex -isolated -f examples/tmp.lit
```
