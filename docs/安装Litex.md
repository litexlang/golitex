# 安装 Litex

Litex 是一个处于 beta 阶段的实验性业余项目，使用中可能遇到不完善之处。

如果希望免安装试用 Litex，可以使用[在线 playground](https://litexlang.com)。

## 安装

当前发布流程构建的安装包同时包含 `litex` 可执行文件和标准库。旧版的目录布局和 CLI 行为可能不同，请核对 `litex -version` 和 `litex -help`。所有发行版本都可以在 [GitHub Releases 页面](https://github.com/litexlang/golitex/releases)找到。

### macOS 和 Linux：使用 Homebrew

先安装 [Homebrew](https://brew.sh)，并完成它要求的 shell/PATH 配置，再执行：

```bash
brew install litexlang/tap/litex
export LITEX_STD_PATH="$(brew --prefix litex)/bin/std"
```

把这条 `export` 写入 shell 启动文件（zsh 使用 `~/.zshrc`，Bash 使用 `~/.bashrc`），供新终端使用。旧版 formula 将标准库放在 `$(brew --prefix litex)/share/litex/std`；若没有 `bin/std`，检查该目录并改用它的绝对路径。已经安装过 Litex 时，可运行 `brew update` 和 `brew upgrade litex` 请求 tap 中的版本；它仍可能与当前开发源码不同。

当前发布流程只为 Apple Silicon 构建 macOS Homebrew 压缩包，并为 Linux 构建 `amd64` 和 `arm64` 压缩包。

### Ubuntu 和 Debian

先用 `dpkg --print-architecture` 查看 Debian 架构，再从[所需发行版](https://github.com/litexlang/golitex/releases)下载匹配的 `.deb`（`amd64` 或 `arm64`）。把下面的文件名占位符替换为实际下载的文件名：

```bash
sudo dpkg -i ./litex_<version>_<architecture>.deb
export LITEX_STD_PATH=/usr/share/litex/std
```

把这条 `export` 写入 shell 启动文件，供新终端使用。

### Windows：使用 Scoop

先安装 [Scoop](https://scoop.sh) 和 Git（若未安装 Git，可用 `scoop install git`），再在普通 PowerShell 终端中运行：

```powershell
scoop bucket add litex https://github.com/litexlang/scoop-litex
scoop install litex
$env:LITEX_STD_PATH = Join-Path (scoop prefix litex) 'std'
[Environment]::SetEnvironmentVariable('LITEX_STD_PATH', $env:LITEX_STD_PATH, 'User')
```

如果不用 Scoop，可以从[所需发行版](https://github.com/litexlang/golitex/releases)下载 Windows `amd64` 压缩包，把 `litex.exe` 和 `std` 一起解压，并把包含 `litex.exe` 的目录添加到用户的 `Path`。将用户环境变量 `LITEX_STD_PATH` 设置为解压后的 `std` 目录的绝对路径。修改用户环境变量后，打开新终端。

例如手动安装在 `C:\Tools\Litex` 时，可同时配置当前终端和后续终端：

```powershell
$env:LITEX_STD_PATH = 'C:\Tools\Litex\std'
[Environment]::SetEnvironmentVariable('LITEX_STD_PATH', $env:LITEX_STD_PATH, 'User')
```

## 可选的 std 导入

当前 `std/basics` 是不导出任何声明的空兼容模块。`quot`、`$dvd` 等原生词汇由内核实现，不需要导入 std 或设置 `LITEX_STD_PATH`。下面的路径配置只在项目显式使用 `[import std]` 时才需要。

把可执行文件加入 `PATH`，并不会配置标准库查找路径。对于 `[import std]`，当前 CLI 优先使用 `LITEX_STD_PATH`，其次查找工作目录中的 `std/`，再查找目标项目中的 `std/`。它不会自动查找已安装可执行文件旁边的标准库。`LITEX_STD_PATH` 应使用 **std 目录**的绝对路径，不是它的父目录或 `basics` 目录。

## 检查安装

检查已安装的版本，并验证一条简单陈述：

```bash
litex -version
litex -e '1 = 1'
```

这两条命令只检查可执行文件，不会使用标准库。下面描述的是当前源码版本的输出；旧安装版的选项和 JSON 字段可能不同。

`-version` 打印一行简短文本。默认英文模式下，`-e` 返回一份 Normal JSON `run` 文档；成功的批量检查以 `0` 退出，且包含 `"success": true` 和 `"session_error": null`。程序若需要英文 JSON 键，请使用 `-lang en`；`-lang zh` 会将这些键本地化。

若要检查安装包中的兼容模块，可在 Litex 源码目录之外新建项目目录，并创建以下两个文件。导入检查的是模块加载；下面两条陈述检查的是内核原生词汇，并不引用 std 中的声明：

`litex.config`：

```ini
[import std]
basics
[export]
smoke = "./smoke.lit"
```

`smoke.lit`：

```litex
quot(-7, 3) = -3
$dvd(12, 3)
```

在该目录执行：

```bash
litex -lang en -f smoke.lit
```

应以 `0` 退出，并包含 `"kind": "run"`、`"success": true` 和 `"session_error": null`。若返回 `"session_error": "failed to import project"`，请先检查 `LITEX_STD_PATH` 指向的目录中是否有 `basics/litex.config`，以及二进制和标准库是否来自同一版本。该消息本身不能区分路径错误和其他导入失败。

如果要检查当前检出的源码，而不是另行安装的发行版，先安装 [Rust/Cargo](https://www.rust-lang.org/tools/install)，再从仓库根目录运行：

```bash
cargo build --release
./target/release/litex -version
./target/release/litex -e '1 = 1'
export LITEX_STD_PATH="$PWD/std"
```

执行上面的外部项目检查时，使用 `target/release/litex` 的绝对路径；裸命令 `litex` 仍可能指向旧安装版。

参考文档描述的是当前检出版本的 `src/` 入口。已安装发行版的命令集可能不同，请对照 `-version` 和 `-help`。

## 入门命令

```bash
litex                              # start the interactive REPL
litex -e '1 + 1 = 2'               # run source directly
litex -f example.lit               # run a project file or standalone file
```

上面三条命令依次启动交互式 REPL、直接运行源码，以及运行项目文件或独立文件。完整的命令、选项、JSON 输出结构、会话选项和项目布局规则，见[完整 CLI 参考](Litex命令行参考.md)。接下来可尝试的短证明，见[示例](../examples/README.md)。
