# Install Litex

Created and maintained by Jiachen Shen.

Try the examples in browser: https://litexlang.com/doc/Setup

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Setup.md

> **Litex is an experimental hobby project still in beta. Expect rough edges.**

## Run Litex online

To quickly try Litex, use the Playground on the official website:

- https://litexlang.com

You can run Litex code there and translate Litex code into LaTeX.

## Install and run Litex locally

Release assets are published on the
[GitHub Releases page](https://github.com/litexlang/golitex/releases). Each
official archive or package contains both the `litex` executable and the
standard library.

After any installation, check both the version and a small verified statement:

```bash
litex -version
litex -e '1 = 1'
```

---

## macOS and Linux (Homebrew)

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

---

## Linux (Ubuntu/Debian)

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

### Upgrade Litex on Linux

If you installed from the `.deb` in Releases, upgrade by downloading the latest tag and installing
it again (this replaces the older version):

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

---

## Windows

### Option A (recommended): Scoop

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

### Option B: direct PowerShell install

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

Now users can run `litex` directly in terminal.

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

---

## Docker

The release workflow publishes multi-architecture Linux images for `amd64` and
`arm64`. Prereleases use the `beta` tag; stable releases also update `latest`.

```bash
docker pull ghcr.io/litexlang/litex:beta
docker run --rm ghcr.io/litexlang/litex:beta -runner -e '1 = 1'
```

Use a version tag such as `0.9.109-beta` when reproducibility matters.

---

## Build from source

For kernel development, install the stable Rust toolchain, clone this
repository, and build from the repository root:

```bash
git clone https://github.com/litexlang/golitex.git
cd golitex
cargo build
target/debug/litex -e '1 = 1'
```

Running from the repository root lets Litex find the checked-in `std`
directory. Packaged installations place the same standard library beside the
binary or in the platform installation directory.

---

## Run Litex on your machine

Start REPL:

```bash
litex
```

The ordinary REPL is always isolated, including when the current directory
contains `litex.config`. It is a persistent terminal environment, not a
project run.

Typical successful output:

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

---

## Command-line options

For the full command-line grammar and current edge-case behavior, see
[`docs/cli.md`](cli.md).

In examples, the executable is written as:

```text
litex [OPTION...]
```

Basic behavior:

- **No arguments**: starts an isolated persistent interactive REPL; it does not discover a current-directory project.
- **With options**: runs code, files, repositories, or helper commands as described below.
- **Unknown options**: print an error message and exit.

| Option | Description |
|--------|-------------|
| `-help` | Print help and exit. |
| `-version` | Print the installed version and exit. |
| `-upgrade` | Print platform-specific upgrade instructions and exit. |
| `-e <code>` | Run a Litex source string. |
| `-f <file>` | Require `litex.config` in the direct parent and run the configured export prefix through this file. |
| `-isolated -f <file>` | Run a standalone file without project discovery, then continue in an isolated REPL after success. |
| `-r <project>` | Run a module's complete recursive `[export]` tree, or the root prefix through a selected submodule. |
| `-runner -e/-f/-r ...` | Run the verifier and return one wrapper JSON object with a meaningful process exit code. |
| `-session` | Start a framed, machine-readable persistent verifier session; use `-f <file>` to include a registered target or `-before <file>` to load only its predecessors and work in the target file environment. |
| `-graph -e/-f/-r ... [json]` | Produce a prop/function/fact relation graph. |
| `-factgraph -e/-f/-r ... [json]` | Produce a fact-only verification dependency graph. |
| `-defgraph -e/-f/-r ... [json]` | Produce an environment-backed definition dependency graph. |
| `-latex -e/-f/-r ...` | Compile Litex source to LaTeX; `-latex` alone starts its interactive REPL. |
| `-python -e/-f/-r ...` | Run the frozen experimental extractor for its supported verified subset. |
| `-compact` | Show only result, statement type, line, and source statement for successful results; any `RuntimeError` is always detailed. |
| `-detail` | Include the full audit trace for successful results and errors, plus raw source paths. |
| `-strict` | Verify configured dependencies and reject user trust or axiom statements. |
| `-trust-before-line <X>` | Preview direct-file development mode: trust top-level statements before the exact header line `X`, then verify from `X`. |
| `-summarize` | Append one final run-summary JSON object after ordinary verifier output. |
| `-lang <code>` | Localize JSON keys and explanatory labels without changing Litex source text. |

Commands that take a value require the next token to be present and not begin
with `-`. Global options such as `-detail`, `-strict`, `-summarize`, and
`-lang` may appear before or after the primary command; putting them first is
usually easiest to read. After `-latex`, use `-f`, `-e`, or `-r` with its
argument; without a selector, `-latex` starts the interactive LaTeX-output
REPL.

Litex supports multiple output languages through `-lang <code>`. See
[`docs/cli.md`](cli.md) for the current list of supported language codes.

For a faster check after editing the latter part of a long file:

```bash
litex -compact -f chapter.lit -trust-before-line 420
```

`420` must be the exact one-based line of a top-level statement header.
Earlier top-level statements are still parsed and added to the environment,
but their proofs and well-definedness checks are skipped. Verification resumes
at line 420. The option is available only for direct `-f` and
`-isolated -f` runs, cannot be combined with `-strict`, and produces explicit
`trusted_prefix` statement statuses rather than a fully checkable result. It
does not propagate trust metadata into the verified suffix. See
[`docs/cli.md`](cli.md#trusted-prefix-file-checks-preview) for the full
contract.

Hint: if your Litex code contains spaces, newlines, or shell-sensitive characters, wrap it in quotes when using `-e`, or put it in a `.lit` file and run it with `-f`.

---

## Command output format

For commands that execute Litex source, such as `-e`, `-f`, and `-r`, Litex
prints one JSON object for each executed statement.
By default, Litex prints the normal reading view: internal statements,
assumptions, conclusions, and direct `why_verified` reasons, without audit
duplication. These output styles control successful results: use `-compact` to
scan only the four base fields for each success, or `-detail` for full success
trace details, execution phases, and raw paths. Every `RuntimeError` is
automatically rendered with the detailed error projection in compact, normal,
and detail modes.

If the whole run succeeds:

- The output contains one JSON object per user statement, separated by newlines; each object describes that statement's outcome.
- Each successful statement object has `"result": "success"`.
- The last JSON object for your source is the last statement that ran successfully.

With `-summarize`, ordinary verifier commands append one extra JSON object at
the end with `"output_type": "run summary"`. The default `-e`, `-f`, and `-r`
output stays statement-only. The summary includes top-level and expanded
statement counts, prop/theorem/fact counts, proof-debt and axiom counts,
`statement_type_counts`, `output_type_counts`, and a `statements` array that
records line numbers for editor-side selection.

This is useful when another program wants to call Litex and inspect whether a
proof or computation succeeded. For scripts and CI, prefer `-runner` because it
also returns a nonzero process exit code when verification fails.

Example success output looks like this. The exact output may differ by version:

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

For most factual statements, `why_verified` is the direct proof route. Detail
output expands the audit information, including local assumptions,
conclusions, nested results, and environment effects when available.

If an error occurs, Litex leaves any earlier successful objects in the selected
style and prints only the failing result with the full available diagnostic.
This applies consistently to file, repository, REPL, runner, session, and
`try:` execution. Detailed errors may include `phases`,
`previous_error`, `failed_step`, `failed_goal`, nested `unknown_result`, step
indexes, and internal execution results. Litex omits fields for information
that the error did not produce instead of inventing placeholder data. Warnings
on otherwise successful statements remain in the selected success style.

The important error fields are usually:

- `"result": "error"`
- `"error_type"`: the broad kind of error, such as parse, verify, or runtime error
- `"message"`: the human-readable reason
- `"previous_error"`: more context, if the error was caused by another error

Hint: programs that call Litex should check the JSON output, not only the process exit code.

Error field names and exit-code behavior are unchanged. Compared with older
compact or normal output, failures may contain additional diagnostic fields,
but retain their existing base fields.

Example error output looks like this. The exact output may differ by version:

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

## Runner output

`litex -runner -e <code>`, `litex -runner -f <file>`, and
`litex -runner -r <project>` run the same verifier but return one wrapper JSON
object for scripts and CI checks.

The wrapper includes:

- `"ok"` and `"result"` for the whole run;
- `"target"` with the requested source kind and label;
- `"error"` with target-read failure information when the source cannot be loaded;
- `"trace"`, containing the ordinary Litex statement-by-statement JSON output.

Unlike the basic `-e`, `-f`, and `-r` commands, the runner exits with a nonzero code when the checked run fails or when the target source cannot be loaded.

---

Visit https://litexlang.com/doc/cli to learn command line commands of Litex.
