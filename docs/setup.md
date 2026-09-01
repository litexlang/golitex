# Set Up Litex

Litex is an experimental hobby project in beta. Expect rough edges.

To try Litex without installing anything, use the
[online playground](https://litexlang.com).

## Install

Official packages contain both the `litex` executable and its standard
library. All releases are available on the
[GitHub Releases page](https://github.com/litexlang/golitex/releases).

### macOS and Linux with Homebrew

```bash
brew install litexlang/tap/litex
```

The current macOS Homebrew package targets Apple Silicon. Linux packages are
available for `amd64` and `arm64`.

### Ubuntu and Debian

Download the `.deb` matching your architecture (`amd64` or `arm64`) from the
[latest release](https://github.com/litexlang/golitex/releases/latest), then
install it:

```bash
sudo dpkg -i litex_<version>_<architecture>.deb
```

### Windows with Scoop

Run these commands in PowerShell:

```powershell
scoop bucket add litex https://github.com/litexlang/scoop-litex
scoop install litex
```

If you do not use Scoop, download the Windows `amd64` archive from the
[latest release](https://github.com/litexlang/golitex/releases/latest), extract
both `litex.exe` and `std`, and add their directory to your user `Path`.

## Verify the installation

Check the installed version and one small statement:

```bash
litex -version
litex -e '1 = 1'
```

Both commands return JSON. The second command should contain `"ok": true`.

## A few commands to start

```bash
litex                              # start the interactive REPL
litex -e '1 + 1 = 2'               # run source directly
litex -f example.lit               # run a project file or standalone file automatically
```

For every command, option, JSON output shape, session protocol, graph command,
and project layout rule, read the [complete CLI reference](cli.md). For small
proofs to try next, see the [examples](../examples/README.md).
