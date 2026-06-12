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

The `.deb` package installs the standard library at `/usr/share/litex/std`.
To verify that the CLI accepts a standard-library import registration, run:

```bash
litex -e $'import Trig' | grep '"statement": "import Trig"'
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
litex -e $'import Trig' | grep '"statement": "import Trig"'
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
$std = Join-Path $dir 'std'

New-Item -ItemType Directory -Force -Path $dir | Out-Null
Invoke-WebRequest -Uri $url -OutFile $zip
if (Test-Path $std) {
    Remove-Item -Recurse -Force $std
}
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
Write-Host "Installed std: $std"
Write-Host "Open a new terminal and run: litex -version"
```

What this command changes on the user machine:

1. Downloads `litex_<tag>_windows_amd64.zip` from GitHub Releases.
2. Writes `litex.exe` to `%LOCALAPPDATA%\litex\litex.exe`.
3. Writes the standard library to `%LOCALAPPDATA%\litex\std`.
4. Appends `%LOCALAPPDATA%\litex` to the **User** `Path` environment variable.
5. Updates `Path` in the current PowerShell session.

It does **not** install services or edit firewall settings.

After running the command:

1. Open a **new** terminal window.
2. Run:

```powershell
litex -version
litex -e "import Trig" | Select-String '"statement": "import Trig"'
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
$std = Join-Path $dir 'std'

New-Item -ItemType Directory -Force -Path $dir | Out-Null
Invoke-WebRequest -Uri $url -OutFile $zip
if (Test-Path $std) {
    Remove-Item -Recurse -Force $std
}
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
litex -e "import Trig" | Select-String '"statement": "import Trig"'
```

### Upgrade Litex on Windows

If you installed by **Option A** (PowerShell one-command install), run the same command again.
It downloads the newer zip, overwrites `%LOCALAPPDATA%\litex\litex.exe`, refreshes
`%LOCALAPPDATA%\litex\std`, and keeps your existing user `Path` entry:

```powershell
$ErrorActionPreference = 'Stop'
$repo = 'litexlang/golitex'
$tag = (Invoke-RestMethod -Uri "https://api.github.com/repos/$repo/releases/latest" -Headers @{ 'User-Agent' = 'litex-install' }).tag_name
$name = "litex_${tag}_windows_amd64.zip"
$url = "https://github.com/$repo/releases/download/$tag/$name"
$dir = Join-Path $env:LOCALAPPDATA 'litex'
$zip = Join-Path $env:TEMP $name
$exe = Join-Path $dir 'litex.exe'
$std = Join-Path $dir 'std'
New-Item -ItemType Directory -Force -Path $dir | Out-Null
Invoke-WebRequest -Uri $url -OutFile $zip
if (Test-Path $std) {
    Remove-Item -Recurse -Force $std
}
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
litex -e "import Trig" | Select-String '"statement": "import Trig"'
```

---

## Run Litex on your machine

Start REPL:

```bash
litex
```

Typical successful output:

```text
Litex version <version>
Upgrade Litex? Run `litex -upgrade` for platform instructions.
Copyright (C) 2024-2026 Jiachen Shen
website: https://litexlang.com
github: https://github.com/litexlang/golitex
Ctrl+D to exit.
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

- **No arguments**: starts the interactive REPL.
- **With options**: runs code, files, repositories, or helper commands as described below.
- **Unknown options**: print an error message and exit.

| Option | Description |
|--------|-------------|
| `-help` | Print help and exit. |
| `-version` | Print the Litex version and exit. |
| `-upgrade` | Print platform upgrade instructions and exit. |
| `-e <code>` | Run a Litex source string. |
| `-f <file>` | Run a file. The path may be relative to the current working directory or absolute. |
| `-r <repo>` | Same as running `<repo>/main.lit`. Place `main.lit` at the repo root. |
| `-runner -e <code>` | Run a source string and return one wrapper JSON object. |
| `-runner -f <file>` | Run a file and return one wrapper JSON object. |
| `-runner -r <repo>` | Run a repository and return one wrapper JSON object. |
| `-detail` | Include full trace details, empty fields, and raw paths for cross-source references. |
| `-latex` | Start an interactive REPL that prints LaTeX output. |
| `-latex -f <file>` | Compile a file to LaTeX, when available. |
| `-latex -e <code>` | Compile a source string to LaTeX, when available. |
| `-fmt <code>` | Format Litex code, when available. |
| `-install <module>` | Install a module, when available. |
| `-uninstall <module>` | Uninstall a module, when available. |
| `-list` | List installed modules, when available. |
| `-update <module>` | Update a module, when available. |
| `-tutorial` | Run the tutorial, when available. |

Options like `-e`, `-f`, `-r`, `-runner -e`, `-runner -f`, `-runner -r`, `-fmt`, `-install`, `-uninstall`, and `-update` require a value that does not start with `-` immediately after the flag. After `-latex`, you may use sub-options `-f`, `-e`, or `-r` with their arguments; without a sub-option, `-latex` starts the interactive LaTeX-output REPL.

Hint: if your Litex code contains spaces, newlines, or shell-sensitive characters, wrap it in quotes when using `-e`, or put it in a `.lit` file and run it with `-f`.

---

## Command output format

For commands that execute Litex source, such as `-e`, `-f`, and `-r`, Litex prints one JSON object for each executed statement.
By default, Litex omits empty arrays and empty strings, and it does not print
raw file paths. Cross-source references still keep safe provenance labels such
as `builtin_code`, `std/Trig`, or `external_file`. Use
`-detail` when you need full trace details and raw paths for debugging.

If the whole run succeeds:

- The output contains one JSON object per user statement, separated by newlines; each object describes that statement's outcome.
- Each successful statement object has `"result": "success"`.
- The last JSON object for your source is the last statement that ran successfully.

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
