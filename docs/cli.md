# Litex CLI

<!-- Blueprint spine: try online → install for one platform → verify the installation → learn the command shape → choose a run mode → inspect or automate the result -->

This is the canonical installation guide and command-line reference for the
Rust `litex` binary.

Created and maintained by Jiachen Shen.

Read this page online: https://litexlang.com/doc/cli

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/cli.md

> **Litex is an experimental hobby project still in beta. Expect rough edges.**

## Try Litex Online

To quickly try Litex without installing it, use the Playground on the official
website:

- https://litexlang.com

You can run Litex code there and translate Litex code into LaTeX.

## Install Litex Locally

Release assets are published on the
[GitHub Releases page](https://github.com/litexlang/golitex/releases). Each
official archive or package contains both the `litex` executable and the
standard library.

After any installation, check both the version and a small verified statement:

```bash
litex -version
litex -e '1 = 1'
```

### macOS and Linux (Homebrew)

Homebrew is the shortest supported installation route on Apple Silicon macOS
and on Linux (`amd64` or `arm64`).

Install:

```bash
brew install litexlang/tap/litex
```

Upgrade:

```bash
brew update
brew upgrade litexlang/tap/litex
```

If upgrade fails or is too slow on your machine, use:

```bash
brew uninstall litex
brew install litexlang/tap/litex
```

The current Homebrew macOS package targets Apple Silicon. For another macOS
architecture, build from source until a matching release asset is available.

### Linux (Ubuntu/Debian)

Official `.deb` packages are available for `amd64` and `arm64`. This command
detects the current Debian architecture and installs the latest release:

```bash
tag=$(curl -fsSL https://api.github.com/repos/litexlang/golitex/releases/latest | grep '"tag_name"' | sed -E 's/.*"([^"]+)".*/\1/')
arch=$(dpkg --print-architecture)
case "$arch" in amd64|arm64) ;; *) echo "Unsupported architecture: $arch"; exit 1 ;; esac
wget "https://github.com/litexlang/golitex/releases/download/${tag}/litex_${tag}_${arch}.deb"
sudo dpkg -i "litex_${tag}_${arch}.deb"
```

If you want a fixed release, replace `<tag>` and `<arch>` (`amd64` or `arm64`)
manually:

```bash
wget "https://github.com/litexlang/golitex/releases/download/<tag>/litex_<tag>_<arch>.deb"
sudo dpkg -i "litex_<tag>_<arch>.deb"
```

If needed, fix dependencies:

```bash
sudo apt-get install -f
```

The `.deb` package installs the Litex executable together with its standard
library. Verify the executable with a checked statement:

```bash
litex -runner -e '1 = 1' | grep '"ok": true'
```

#### Upgrade Litex on Linux

If you installed from the `.deb` in Releases, upgrade by downloading the
latest tag and installing it again. This replaces the older version:

```bash
tag=$(curl -fsSL https://api.github.com/repos/litexlang/golitex/releases/latest | grep '"tag_name"' | sed -E 's/.*"([^"]+)".*/\1/')
arch=$(dpkg --print-architecture)
case "$arch" in amd64|arm64) ;; *) echo "Unsupported architecture: $arch"; exit 1 ;; esac
wget "https://github.com/litexlang/golitex/releases/download/${tag}/litex_${tag}_${arch}.deb"
sudo dpkg -i "litex_${tag}_${arch}.deb"
```

Then verify:

```bash
litex -version
litex -runner -e '1 = 1' | grep '"ok": true'
```

### Windows

#### Option A (recommended): Scoop

The release workflow keeps the Litex Scoop bucket up to date. In PowerShell:

```powershell
scoop bucket add litex https://github.com/litexlang/scoop-litex
scoop install litex
```

Upgrade later with:

```powershell
scoop update
scoop update litex
```

#### Option B: direct PowerShell install

If you do not use Scoop, this script installs the latest release under
`%LOCALAPPDATA%\litex` and adds that directory to the user `Path`:

```powershell
$ErrorActionPreference = 'Stop'
$repo = 'litexlang/golitex'
$tag = (Invoke-RestMethod -Uri "https://api.github.com/repos/$repo/releases/latest" -Headers @{ 'User-Agent' = 'litex-install' }).tag_name
$name = "litex_${tag}_windows_amd64.zip"
$url = "https://github.com/$repo/releases/download/$tag/$name"
$dir = Join-Path $env:LOCALAPPDATA 'litex'
$zip = Join-Path $env:TEMP $name
$exe = Join-Path $dir 'litex.exe'
New-Item -ItemType Directory -Force -Path $dir | Out-Null
Invoke-WebRequest -Uri $url -OutFile $zip
Expand-Archive -Path $zip -DestinationPath $dir -Force
Remove-Item -Force $zip

$userPath = [Environment]::GetEnvironmentVariable('Path', 'User')
if (-not $userPath) { $userPath = '' }
if ($userPath -notlike "*$dir*") {
    $newPath = if ($userPath) { "$userPath;$dir" } else { $dir }
    [Environment]::SetEnvironmentVariable('Path', $newPath, 'User')
}

$env:Path = "$dir;$env:Path"
Write-Host "Installed: $exe"
Write-Host "Open a new terminal and run: litex -version"
```

What this command changes on the user machine:

1. Downloads `litex_<tag>_windows_amd64.zip` from GitHub Releases.
2. Extracts `litex.exe` and the `std` directory into `%LOCALAPPDATA%\litex`.
3. Appends `%LOCALAPPDATA%\litex` to the **User** `Path` environment variable.
4. Updates `Path` in the current PowerShell session.

It does **not** install services or edit firewall settings.

After running the command:

1. Open a **new** terminal window.
2. Run:

```powershell
litex -version
litex -runner -e "1 = 1" | Select-String '"ok": true'
```

Now users can run `litex` directly in a terminal.

If you want a fixed tag, replace `<tag>` manually:

```powershell
$ErrorActionPreference = 'Stop'
$tag = '<tag>'
$repo = 'litexlang/golitex'
$name = "litex_${tag}_windows_amd64.zip"
$url = "https://github.com/$repo/releases/download/$tag/$name"
$dir = Join-Path $env:LOCALAPPDATA 'litex'
$zip = Join-Path $env:TEMP $name
$exe = Join-Path $dir 'litex.exe'
New-Item -ItemType Directory -Force -Path $dir | Out-Null
Invoke-WebRequest -Uri $url -OutFile $zip
Expand-Archive -Path $zip -DestinationPath $dir -Force
Remove-Item -Force $zip

$userPath = [Environment]::GetEnvironmentVariable('Path', 'User')
if (-not $userPath) { $userPath = '' }
if ($userPath -notlike "*$dir*") {
    $newPath = if ($userPath) { "$userPath;$dir" } else { $dir }
    [Environment]::SetEnvironmentVariable('Path', $newPath, 'User')
}

$env:Path = "$dir;$env:Path"
litex -version
litex -e "1 = 1" | Select-String '"result": "success"'
```

To upgrade a direct PowerShell installation, rerun the same script. It replaces
the executable and bundled `std` directory while preserving the existing
`Path` entry.

### Docker

The release workflow publishes multi-architecture Linux images for `amd64` and
`arm64`. Prereleases use the `beta` tag; stable releases also update `latest`.

```bash
docker pull ghcr.io/litexlang/litex:beta
docker run --rm ghcr.io/litexlang/litex:beta -runner -e '1 = 1'
```

Use a version tag such as `0.9.109-beta` when reproducibility matters.

### Build from Source

For kernel development, install the stable Rust toolchain, clone this
repository, and build from the repository root:

```bash
git clone https://github.com/litexlang/golitex.git
cd golitex
cargo build --release
target/release/litex -e '1 = 1'
```

Running from the repository root lets Litex find the checked-in `std`
directory. Packaged installations place the same standard library beside the
binary or in the platform installation directory.

## First Run

Start the REPL:

```bash
litex
```

The ordinary REPL is always isolated, including when the current directory
contains `litex.config`. It is a persistent terminal environment, not a
project run.

Typical startup output:

```text
Litex version <version>
Upgrade Litex? Run `litex -upgrade` for platform instructions.
Copyright (C) 2024-2026 Jiachen Shen
website: https://litexlang.com
github: https://github.com/litexlang/golitex
Ctrl+D to exit. On Windows PowerShell, press Ctrl+Z and then Enter.
>>>
```

Run a standalone `.lit` file:

```bash
litex -isolated -f "your_file.lit"
```

For a file registered in a module's direct-parent `litex.config`, use
`litex -f "your_file.lit"` to load its configured source prefix first.

Run Litex source directly:

```bash
litex -e "1 + 1 = 2"
```

Show the installed version and platform upgrade instructions:

```bash
litex -version
litex -upgrade
```

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
litex -compact -session -before chapter.lit
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
| `-summarize` | Append one final run-summary JSON object after ordinary verifier command output. |
| `-lang <code>` | Localize JSON keys and explanatory labels. Mathematical source strings inside fields such as `statement`, `fact`, and `cited_statement` stay in Litex syntax. |

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

Because `-compact`, `-detail`, `-strict`, and `-summarize` are removed globally
before command parsing, do not use a standalone command value exactly equal to
any of those flags. `-lang` also consumes the next token globally.

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

## Lean Compiler Commands

| Command | Behavior |
|---------|----------|
| `litex -isolated -f <input.lit> -lean <output.lean>` | Verify and compile one Litex source file into one complete Lean file. The output is replaced only after the complete source compiles successfully. |
| `litex -lean-ledger <input.md> <output.lean>` | Freshly compile every `litex` fence under a level-two Markdown heading and combine the results in numbered namespaces. |

The canonical single-file tracer can be generated through either the main CLI
or the dedicated compiler wrapper:

```bash
litex -lean \
  lean/examples/1_SetSystem.lit \
  lean/examples/1_SetSystem.lean

./lean/stmt_result_to_lean_compiler.sh compile lean/examples/1_SetSystem.lit
```

Declaration-bearing `sketch` blocks compile into isolated Lean namespaces.
This preserves source order without leaking names between examples. Unsupported
or trusted routes fail closed; the compiler does not emit `sorry` or project
axioms.

Declare local project files and child submodules in recursive ordered
`[export]` entries. Only a `[hierarchy] module` declares non-standard packages
in `[import]` or installed packages in `[import std]`. Files cite canonical
names such as `Part2::chap3::theorem` or
`basics::theorem`. No `.lit` source file can write imports; this includes
standalone files run with `-isolated -f`.

Manifest authors may opt selected sources into recursive bare-symbol lookup:

```ini
[allow bare export]
Part2

[allow bare import std]
basics

[allow bare import]
Algebra
```

Each name must occur in its matching table; an allow-bare export must be a
folder/submodule. The default remains qualified-only. Enabled sources expose
only terminal symbols in their recursive public `[export]` trees, after those
targets are loaded; private imports are not re-exported.

The ordinary REPL, and the continued terminal after a successful isolated
`-f`, may load further interfaces dynamically with terminal commands:

<!-- litex:skip-test -->
```text
litex> import "../Algebra" as Algebra
litex> Algebra::implementation::some_fact
litex> import std basics
litex> basics::some_fact
```

The quoted target must be a folder whose `litex.config` declares
`[hierarchy] module`. The import runs that module's declared imports and full
ordered `[export]` tree. Conceptually, each command appends a dependency to an
invisible, in-memory `litex.config` owned by that REPL. It is not written to
disk, disappears when the process exits, and never becomes a Litex statement
or statement Result. For reproducible source, declare the dependency in the
real project manifest.

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
Only successfully committed statements contribute to these counts. A failed
atomic `trust` or `trust have` remains visible in the error object, but its
staged facts, bindings, and inference do not appear in the environment summary
or graph artifacts. An earlier, separately successful statement remains part
of the successful prefix.
Prefer:

```bash
litex -summarize -isolated -f examples/tmp.lit
```

Ordinary verifier commands are designed for interactive inspection. Programs
should read the JSON result instead of relying only on the process exit code.
Use `-runner` when a script or CI job needs a wrapper object and a nonzero exit
code on verification failure.

### Statement Output Examples

A successful statement object has `"result": "success"`. The normal reading
view includes its direct proof route when one is available:

```json
{
  "result": "success",
  "type": "equality fact",
  "line": 1,
  "statement": "1 + 1 = 2",
  "why_verified": {
    "type": "builtin rule",
    "rule": "calculation"
  }
}
```

If an error occurs, the most useful fields are usually `error_type`, `message`,
`statement`, and `previous_error`. The exact output may differ by version:

```json
{
  "error_type": "VerifyError",
  "result": "error",
  "line": 1,
  "message": "verification failed",
  "type": "equality fact",
  "statement": "1 = 0",
  "previous_error": {
    "error_type": "UnknownError",
    "result": "error",
    "line": 1,
    "message": "unknown result",
    "type": "equality fact",
    "statement": "1 = 0",
    "failed_goal": "1 = 0"
  }
}
```

Programs should inspect the JSON rather than rely on an ordinary verifier
command's process status. Use the runner commands below when a meaningful
nonzero exit code is part of the calling contract.

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

Session `run` frames are Litex source, not terminal input. They reject
`import`, and the protocol intentionally defines no separate import frame;
dependencies for a session come from its `litex.config` preload.

A parsed top-level `try:` block always returns a `block` event with `ok: true`.
Its statement result reports whether the isolated body was `Committed` or
`RolledBack`; a rollback keeps its diagnostic but publishes no environment
changes. The client may submit another `run` frame, and `artifacts` remains
available. A malformed source frame that never parses as a `try` is an ordinary
source error. Like any other failed Litex statement, it stops later frames:
subsequent `run` requests return `skipped`, and `artifacts` returns
`artifacts_unavailable`. A `try:` nested inside another top-level statement does
not make a parse failure in that outer statement recoverable.

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
3. A committed `try:` publishes its definitions and facts to the persistent
   Runtime. A rolled-back `try:` discards only that candidate, so the chap1--chap4
   prefix and all earlier committed chap5 frames remain available.
4. Correct and resend only the failed fragment. If a proof remains blocked,
   keep its intended statement and use the narrowest explicit `trust` before
   continuing with the next statement.
5. Write each accepted statement back to `chap5.lit`. When all fragments have
   been replayed, run release `-f chap5.lit` once as the clean file checkpoint.

A rolled-back `try:` never requires a restart. Restart from `-before chap5.lit` only
if the process exits, a loaded predecessor changes, or an already committed
definition must be replaced under the same name.

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
| `litex -graph -e <code> <json>` | Run a source string and save one recursive statement-result/proof/FactId graph JSON object. |
| `litex -graph -f <file> <json>` | Run a file and save one recursive statement-result/proof/FactId graph JSON object. |
| `litex -graph -r <repo> <json>` | Discover the repository module graph, run its ordered `[export]` table, and save one recursive statement-result/proof/FactId graph JSON object. |
| `litex -factgraph -e <code> <json>` | Run a source string and save a fact-only verification dependency graph. |
| `litex -factgraph -f <file> <json>` | Run a file and save a fact-only verification dependency graph. |
| `litex -factgraph -r <repo> <json>` | Discover the repository module graph, run its ordered `[export]` table, and save a fact-only verification dependency graph. |
| `litex -defgraph -e <code> <json>` | Run a source string and save an environment-backed definition dependency graph. |
| `litex -defgraph -f <file> <json>` | Run a file and save an environment-backed definition dependency graph. |
| `litex -defgraph -r <repo> <json>` | Discover the repository module graph, run its ordered `[export]` table, and save an environment-backed definition dependency graph. |

The main graph is `litex-result-graph` version 2. It walks the recursive
`StmtResult` value directly and creates nodes for statement, well-definedness,
verification, proof, store, store-effect, inference, and fact layers. Tree
edges preserve result-field order; semantic citation, premise, conclusion, and
stored-fact edges use `FactId`, while memo reuse points to the exact shared
proof node. The wrapper includes a `summary`, machine-readable `nodes` and
`edges`, and a Mermaid `flowchart LR` string for quick rendering.
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

`-defgraph` inventories definitions from the final Runtime environment and
records their dependency and provenance edges. Like the other graph commands,
it prints JSON to stdout when the final output path is omitted.

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

## Python Commands

| Command | Behavior |
|---------|----------|
| `litex -python -e <code>` | Verify a source string and emit Python for the extractor's supported definitions. |
| `litex -python -f <file>` | Verify a file and emit Python for the extractor's supported definitions. |
| `litex -python -r <repo>` | Verify a repository's ordered `[export]` table and emit Python for the extractor's supported definitions. |

The Python extractor is a frozen experiment, not a general Litex-to-Python
compiler. It currently emits supported numeric assignments and `algo`
definitions, reports when no extractable definitions exist, and rejects known
unsupported native-complex and number-theory forms instead of approximating
them.

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
- list every direct child `.lit` file and module folder exactly once, in
  mathematical order, under `[export]`; the reserved local `.drafts/`
  directory is ignored by module discovery;
- declare external module folders under `[import]` and installed packages under
  `[import std]`, only in the top-level module;
- cite earlier entries with their canonical export path, such as
  `Part2::chap7::name` or `basics::name`.
- optionally list selected export submodules, standard imports, or path imports
  under `[allow bare export]`, `[allow bare import std]`, or
  `[allow bare import]` respectively.

A configured folder may contain `litex.config`, non-Litex sidecar files, the
direct module children listed in `[export]`, and an optional local `.drafts/`
directory. Exported folders must be submodules. Every other direct child
directory and `.lit` file remains an error. Imported targets must be external
module folders; imports cannot target files, submodules, or descendants of the
importing module.

`-r` and `-f` share one recursive left-to-right order. Running a top-level
module runs the whole tree. Running a submodule traces back to its module,
executes every preceding entry, then executes the selected submodule in full.
Running a registered file follows the same prefix and stops after that file.
`litex -f` requires the file's direct parent to have `litex.config`; use
`litex -isolated -f` for a standalone file.

Dependency order is the recursive `[export]` order. A `module` with exactly
one `.lit` export may write `[module]` then `flatten = true`; its public
interface omits that export-name segment. `std/basics` uses this form, so `[import std] basics` exposes
`basics::name`. Source-level `import` is rejected everywhere; project source
uses its manifest, while only an interactive terminal recognizes import commands.

Each `[import]` declaration creates a private module instance. Two aliases of
one physical folder remain distinct, and imports internal to an imported module
do not become public to its importer.

Allow-bare lookup is a per-file index, not a fallback global search. It scans
each enabled public tree once and requires every terminal name to identify one
unique symbol. Different symbols with the same terminal name are a configuration
error; no later source overwrites an earlier one. Explicit `A::name` always
bypasses this index. Module aliases are a separate namespace from symbols, but
an active external bare symbol reserves its spelling against every local symbol
or binder in that source file; struct fields remain separate. Permissions from
ancestor manifests are inherited by descendant submodules. A later export is
not active in an earlier file, and terminal imports never enable bare lookup.

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

Generate a recursive result graph:

```bash
litex -graph -f examples/04_case_studies/gcd_from_finite_divisors.lit tmp/graphs/gcd_graph.json
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
