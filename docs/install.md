# Install Litex

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

---

## Windows

### Option A (recommended): one command in PowerShell

Run this command in **PowerShell**:

```powershell
$ErrorActionPreference = 'Stop'
$repo = 'litexlang/golitex'
$tag = (Invoke-RestMethod -Uri "https://api.github.com/repos/$repo/releases/latest" -Headers @{ 'User-Agent' = 'litex-install' }).tag_name
$name = "litex_${tag}_windows_amd64.exe"
$url = "https://github.com/$repo/releases/download/$tag/$name"
$dir = Join-Path $env:LOCALAPPDATA 'litex'
$exe = Join-Path $dir 'litex.exe'

New-Item -ItemType Directory -Force -Path $dir | Out-Null
Invoke-WebRequest -Uri $url -OutFile $exe

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

1. Downloads `litex_<tag>_windows_amd64.exe` from GitHub Releases.
2. Writes one file to `%LOCALAPPDATA%\litex\litex.exe`.
3. Appends `%LOCALAPPDATA%\litex` to the **User** `Path` environment variable.
4. Updates `Path` in the current PowerShell session.

It does **not** install services or edit firewall settings.

After running the command:

1. Open a **new** terminal window.
2. Run:

```powershell
litex -version
```

Now users can run `litex` directly in terminal.

If you want a fixed tag (for example a beta tag), use:

```powershell
$ErrorActionPreference = 'Stop'
$tag = '0.9.73-beta'
$repo = 'litexlang/golitex'
$name = "litex_${tag}_windows_amd64.exe"
$url = "https://github.com/$repo/releases/download/$tag/$name"
$dir = Join-Path $env:LOCALAPPDATA 'litex'
$exe = Join-Path $dir 'litex.exe'

New-Item -ItemType Directory -Force -Path $dir | Out-Null
Invoke-WebRequest -Uri $url -OutFile $exe

$userPath = [Environment]::GetEnvironmentVariable('Path', 'User')
if (-not $userPath) { $userPath = '' }
if ($userPath -notlike "*$dir*") {
    $newPath = if ($userPath) { "$userPath;$dir" } else { $dir }
    [Environment]::SetEnvironmentVariable('Path', $newPath, 'User')
}

$env:Path = "$dir;$env:Path"
litex -version
```

### Option B: MSI installer

Users can also install with MSI from Releases, for example:

- https://github.com/litexlang/golitex/releases/download/0.9.73-beta/litex_0.9.73-beta_amd64.msi

Then run the installer wizard.

---

## Run Litex on your machine

Start REPL:

```bash
litex
```

Typical successful output:

```text
Litex-beta - Type your code or 'exit' to quit
Warning: not yet ready for production use.
>>>
```

Run a `.lit` file:

```bash
litex -f "your_file.lit"
```
