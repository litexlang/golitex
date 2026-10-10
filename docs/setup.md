# Set Up Litex

Litex is an experimental hobby project in beta. Expect rough edges.

To try Litex without installing anything, use the
[online playground](https://litexlang.com).

## Install

Packages built by the current release workflow contain both the `litex`
executable and its standard library. Older releases can have different layouts
and CLI behavior; check `litex -version` and `litex -help`. All releases are
available on the
[GitHub Releases page](https://github.com/litexlang/golitex/releases).

### macOS and Linux with Homebrew

Install [Homebrew](https://brew.sh) first and complete its shell/PATH setup.
Then run:

```bash
brew install litexlang/tap/litex
export LITEX_STD_PATH="$(brew --prefix litex)/bin/std"
```

Keep that `export` line in your shell startup file (`~/.zshrc` for zsh or
`~/.bashrc` for Bash) to reuse it in new terminals. Older formulas placed std
under `$(brew --prefix litex)/share/litex/std`; if `bin/std` is absent, check
that directory and use its absolute path instead. If Litex is already
installed, use `brew update` and `brew upgrade litex` to request the tap version;
this may still differ from the current development checkout.

The current release workflow builds the macOS Homebrew archive for Apple
Silicon only, and Linux archives for `amd64` and `arm64`.

### Ubuntu and Debian

Check your Debian architecture with `dpkg --print-architecture`. Download
the matching `.deb` (`amd64` or `arm64`) from the
[release you want](https://github.com/litexlang/golitex/releases), then install
it. Replace the filename placeholders with the downloaded filename:

```bash
sudo dpkg -i ./litex_<version>_<architecture>.deb
export LITEX_STD_PATH=/usr/share/litex/std
```

Keep the `export` line in your shell startup file for new terminals.

### Windows with Scoop

Install [Scoop](https://scoop.sh) and Git first (use `scoop install git` if
Git is missing). In a regular PowerShell terminal, run:

```powershell
scoop bucket add litex https://github.com/litexlang/scoop-litex
scoop install litex
$env:LITEX_STD_PATH = Join-Path (scoop prefix litex) 'std'
[Environment]::SetEnvironmentVariable('LITEX_STD_PATH', $env:LITEX_STD_PATH, 'User')
```

If you do not use Scoop, download the Windows `amd64` archive from the
[chosen release](https://github.com/litexlang/golitex/releases), extract
both `litex.exe` and `std` together, and add the directory containing
`litex.exe` to your user `Path`. Set the user environment variable
`LITEX_STD_PATH` to the absolute path of that extracted `std` directory.
Open a new terminal after changing user environment variables.

For a manual installation at `C:\Tools\Litex`, set the current terminal and
future terminals with:

```powershell
$env:LITEX_STD_PATH = 'C:\Tools\Litex\std'
[Environment]::SetEnvironmentVariable('LITEX_STD_PATH', $env:LITEX_STD_PATH, 'User')
```

## Optional std imports

The current `std/basics` is an empty compatibility module; it exports no
declarations. Native vocabulary such as `quot` and `$dvd` is implemented in
the kernel and works without importing std or setting `LITEX_STD_PATH`.
The paths below matter only when a project explicitly uses `[import std]`.

Adding the executable to `PATH` does not configure standard-library discovery.
For `[import std]`, the current CLI first uses `LITEX_STD_PATH`, then a `std/`
directory in the working directory, then `std/` in the target project. It does
not automatically search beside the installed executable. Use an absolute
`LITEX_STD_PATH` pointing to the **std directory**, not its parent or `basics`.

## Verify the installation

Check the installed version and one small statement:

```bash
litex -version
litex -e '1 = 1'
```

These commands check the executable; they do not exercise the standard library.
The output below describes the current checkout. Older installed versions may
have different flags and JSON fields.

`-version` prints a short text line. `-e` returns one Normal JSON `run`
document in the default English mode; a successful batch check exits `0`
and has `"success": true` with `"session_error": null`. Use `-lang en` for
programs expecting English JSON keys; `-lang zh` localizes them.

To check the packaged compatibility module, create a new project directory
outside the Litex checkout and these two files. The import exercises module
loading; the two statements exercise native vocabulary, not std declarations:

`litex.config`:

```ini
[import std]
basics
[export]
smoke = "./smoke.lit"
```

`smoke.lit`:

```litex
quot(-7, 3) = -3
$dvd(12, 3)
```

From that directory, run:

```bash
litex -lang en -f smoke.lit
```

Require exit `0`, `"kind": "run"`, `"success": true`, and
`"session_error": null`. If the result says
`"session_error": "failed to import project"`, first check that
`LITEX_STD_PATH` contains `basics/litex.config` and that the binary and std
come from the same release. That message alone does not distinguish a path
error from other import failures.

To check this checkout rather than a separately installed release, install
[Rust/Cargo](https://www.rust-lang.org/tools/install) and run from the repository
root:

```bash
cargo build --release
./target/release/litex -version
./target/release/litex -e '1 = 1'
export LITEX_STD_PATH="$PWD/std"
```

Use the absolute path of `target/release/litex` for the external-project check
above; the bare `litex` command can still resolve to an older installed version.

The reference documents describe this checkout’s `src/` entrypoint. An installed
release can have a different command set; compare `-version` and `-help`.

## A few commands to start

```bash
litex                              # start the interactive REPL
litex -e '1 + 1 = 2'               # run source directly
litex -f example.lit               # run a project file or standalone file
```

For every command, option, JSON output shape, session flag, and project layout
rule, read the [complete CLI reference](cli.md). For small proofs to try next,
see the [examples](../examples/README.md).
