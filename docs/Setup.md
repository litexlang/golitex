# Install Litex

Jiachen Shen and The Litex Team, 2026-05-06. Email: litexlang@outlook.com

Try the examples in browser: https://litexlang.com/doc/Setup

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Setup.md


## Run Litex online

To quickly try Litex, use the Playground on the official website:

- https://litexlang.com

You can run Litex code there and translate Litex code into LaTeX.

## Install and run Litex locally

Release assets are published at:

- https://github.com/litexlang/golitex/releases

---

## macOS (Homebrew)

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

---

## Linux (Ubuntu/Debian)

Install latest release automatically (amd64):

```bash
tag=$(curl -fsSL https://api.github.com/repos/litexlang/golitex/releases/latest | grep '"tag_name"' | sed -E 's/.*"([^"]+)".*/\1/')
wget "https://github.com/litexlang/golitex/releases/download/${tag}/litex_${tag}_amd64.deb"
sudo dpkg -i "litex_${tag}_amd64.deb"
```

If you want a fixed tag, replace `<tag>` manually:

```bash
wget "https://github.com/litexlang/golitex/releases/download/<tag>/litex_<tag>_amd64.deb"
sudo dpkg -i "litex_<tag>_amd64.deb"
```

If needed, fix dependencies:

```bash
sudo apt-get install -f
```

The `.deb` package installs the Litex executable together with its standard
library. Verify the executable with a checked statement:

```bash
litex -e '1 = 1' | grep '"result": "success"'
```

### Upgrade Litex on Linux

If you installed from the `.deb` in Releases, upgrade by downloading the latest tag and installing
it again (this replaces the older version):

```bash
tag=$(curl -fsSL https://api.github.com/repos/litexlang/golitex/releases/latest | grep '"tag_name"' | sed -E 's/.*"([^"]+)".*/\1/')
wget "https://github.com/litexlang/golitex/releases/download/${tag}/litex_${tag}_amd64.deb"
sudo dpkg -i "litex_${tag}_amd64.deb"
```

Then verify:

```bash
litex -version
litex -e '1 = 1' | grep '"result": "success"'
```

---

## Windows

### Option A (recommended): one command in PowerShell

Run this command in **PowerShell**:

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
litex -e "1 = 1" | Select-String '"result": "success"'
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

### Upgrade Litex on Windows

If you installed by **Option A** (PowerShell one-command install), run the same command again.
It downloads the newer zip, refreshes `%LOCALAPPDATA%\litex\litex.exe` and its
`std` directory, and keeps your existing user `Path` entry:

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
litex -version
litex -e "1 = 1" | Select-String '"result": "success"'
```

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

Run a `.lit` file:

```bash
litex -f "your_file.lit"
```

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
| `-version` | Print the Litex version and exit. |
| `-upgrade` | Print platform upgrade instructions and exit. |
| `-e <code>` | Run a Litex source string. |
| `-f <file>` | If its direct parent has `litex.config`, trace to the module and run the recursive export prefix through this file; otherwise run it and continue in an isolated REPL with the resulting environment. |
| `-isolated -f <file>` | Force a file to run without project discovery. |
| `-isolated` | Compatibility spelling for the ordinary isolated REPL. |
| `-r <project>` | Run a module's whole recursive export tree, or the root prefix through a selected submodule's whole subtree. |
| `-runner -e <code>` | Run a source string and return one wrapper JSON object. |
| `-runner -f <file>` | Run a file and return one wrapper JSON object. |
| `-runner -r <project>` | Run a project and return one wrapper JSON object. |
| `-session` | Start a framed, machine-readable persistent verifier session; see `docs/cli.md` for its input protocol. |
| `-compact` | Show only result, statement type, line, and source statement. |
| `-detail` | Include full proof details, execution phases, empty fields, and raw paths for cross-source references. |
| `-summarize` | Append one final run-summary JSON object after ordinary verifier output. |
| `-lang <code>` | Localize JSON keys and explanatory labels. Litex code inside `statement`, `fact`, and related fields stays unchanged. |
| `-latex` | Start an interactive REPL that prints LaTeX output. |
| `-latex -f <file>` | Compile a file to LaTeX, when available. |
| `-latex -e <code>` | Compile a source string to LaTeX, when available. |
| `-fmt <code>` | Format Litex code, when available. |
| `-install <module>` | Install a module, when available. |
| `-uninstall <module>` | Uninstall a module, when available. |
| `-list` | List installed modules, when available. |
| `-update <module>` | Update a module, when available. |
| `-tutorial` | Run the tutorial, when available. |

Options like `-e`, `-f`, `-r`, `-runner -e`, `-runner -f`, `-runner -r`, `-lang`, `-fmt`, `-install`, `-uninstall`, and `-update` require a value that does not start with `-` immediately after the flag. After `-latex`, you may use sub-options `-f`, `-e`, or `-r` with their arguments; without a sub-option, `-latex` starts the interactive LaTeX-output REPL.

Litex supports multiple output languages through `-lang <code>`. See
[`docs/cli.md`](cli.md) for the current list of supported language codes.

Hint: if your Litex code contains spaces, newlines, or shell-sensitive characters, wrap it in quotes when using `-e`, or put it in a `.lit` file and run it with `-f`.

---

## Command output format

For commands that execute Litex source, such as `-e`, `-f`, and `-r`, Litex prints one JSON object for each executed statement.
By default, Litex prints the normal reading view: internal statements,
assumptions, conclusions, and direct `why_verified` reasons, without audit
duplication. Use `-compact` to scan only the four base fields, or `-detail`
for full trace details and raw paths. Detailed statement output includes
`phases.verify_well_definedness`, `phases.verify_process`, and
`phases.affect_environment`; facts added to the environment appear as
`affect_environment.effects`, not as a top-level `store_facts` field.

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

This is useful when another program wants to call Litex and inspect whether a proof or computation succeeded.

Example success output looks like this. The exact output may differ by version:

```json
{
  "result": "success",
  "line": 1,
  "statement": "1 + 1 = 2",
  "verification": {
    "type": "builtin rule",
    "rule": "calculation"
  }
}
```

For most factual statements, `verification` is the proof route. Composite proofs
can put sub-checks in `verification.steps`. A successful `forall` fact reports
`conclusions`, with each conclusion carrying a `verification` object; detail
output additionally expands the local `parameters` and `assumptions`.
Successful non-factual statements, such as definitions or proof
blocks, report context changes under `effects`; detail output can expand nested
`inside_results` when available.

If an error occurs, Litex prints an error JSON object. The important fields are usually:

- `"result": "error"`
- `"error_type"`: the broad kind of error, such as parse, verify, or runtime error
- `"message"`: the human-readable reason
- `"previous_error"`: more context, if the error was caused by another error

Hint: programs that call Litex should check the JSON output, not only the process exit code.

Example error output looks like this. The exact output may differ by version:

```json
{
  "error_type": "VerifyError",
  "result": "error",
  "line": 1,
  "message": "verification failed",
  "statement": "1 = 0",
  "previous_error": {
    "error_type": "UnknownError",
    "result": "error",
    "line": 1,
    "statement": "1 = 0"
  }
}
```

## Runner output

`litex -runner -e <code>`, `litex -runner -f <file>`, and `litex -runner -r <repo>` run the same verifier but return one wrapper JSON object for scripts and CI checks.

The wrapper includes:

- `"ok"` and `"result"` for the whole run;
- `"target"` with the requested source kind and label;
- `"error"` with target-read failure information when the source cannot be loaded;
- `"trace"`, containing the ordinary Litex statement-by-statement JSON output.

Unlike the basic `-e`, `-f`, and `-r` commands, the runner exits with a nonzero code when the checked run fails or when the target source cannot be loaded.

---

## Commands that may still be unavailable

Some helper commands, such as LaTeX output, formatting, module management, or tutorial mode, may be unavailable in a particular build. When a command is not available, Litex may print a plain-text placeholder message instead of the JSON stream used for source execution.
