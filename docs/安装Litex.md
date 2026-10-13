# 安装 Litex

Litex 是一个处于 beta 阶段的实验性业余项目，使用中可能遇到不完善之处。

如果希望免安装试用 Litex，可以使用[在线 playground](https://litexlang.com)。

## 安装

当前发布流程构建的安装包同时包含 `litex` 可执行文件和标准库。旧版的目录布局和 CLI 行为可能不同，请核对 `litex -version` 和 `litex -help`。所有发行版本都可以在 [GitHub Releases 页面](https://github.com/litexlang/golitex/releases)找到。

### macOS 和 Linux：使用 Homebrew

先安装 [Homebrew](https://brew.sh)，并完成它要求的 shell/PATH 配置，再执行：

```bash
brew install litexlang/tap/litex
```

当前源码版本会自动查找随可执行文件安装的 std；这些安装布局不需要设置 `LITEX_STD_PATH`。已经安装过 Litex 时，可运行 `brew update` 和 `brew upgrade litex`；tap 中的版本仍可能与当前开发源码不同。

当前发布流程只为 Apple Silicon 构建 macOS Homebrew 压缩包，并为 Linux 构建 `amd64` 和 `arm64` 压缩包。

### Ubuntu 和 Debian

先用 `dpkg --print-architecture` 查看 Debian 架构，再从[所需发行版](https://github.com/litexlang/golitex/releases)下载匹配的 `.deb`（`amd64` 或 `arm64`）。把下面的文件名占位符替换为实际下载的文件名：

```bash
sudo dpkg -i ./litex_<version>_<architecture>.deb
```

### Windows：使用 Scoop

先安装 [Scoop](https://scoop.sh) 和 Git（若未安装 Git，可用 `scoop install git`），再在普通 PowerShell 终端中运行：

```powershell
scoop bucket add litex https://github.com/litexlang/scoop-litex
scoop install litex
```

如果不用 Scoop，可以从[所需发行版](https://github.com/litexlang/golitex/releases)下载 Windows `amd64` 压缩包，把 `litex.exe` 和 `std` 一起解压，并把包含 `litex.exe` 的目录添加到用户的 `Path`。修改用户 `Path` 后打开新终端。保持 std 与可执行文件一起解压；程序会自动找到它。

发布流程还会构建包含可执行文件和 std 的 Windows MSI；MSI 安装和导入检查必须通过，才能作为 GitHub Release 附件发布。这里描述的是当前源码的打包行为；下载旧安装包时，应核对版本。

## 可选的 std 导入

当前 `std/basics` 是不导出任何声明的空兼容模块。`quot`、`$dvd` 等原生词汇由内核实现，不需要导入 std 或设置 `LITEX_STD_PATH`。下面的路径配置只在项目显式使用 `[import std]` 时才需要。

对于 `[import std]`，查找顺序是：显式设置的 `LITEX_STD_PATH`、工作目录的 `std/`、目标项目的 `std/`、真实可执行文件对应安装目录中的 std。程序会跟随符号链接，包括 Homebrew 指向具体安装版本的链接。支持压缩包/Scoop 的 `std/`、Homebrew 的 `bin/std/`、MSI 应用目录的 `std/` 和 Debian 的 `/usr/share/litex/std` 布局。

`LITEX_STD_PATH` 是自定义库或旧二进制使用的可选覆盖路径，应指向 **std 目录**的绝对路径，不是其父目录或 `basics`。显式设置了错误路径时会报错，不会悄悄换用另一份库。当前源码也会自动识别旧 formula 的 `share/litex/std` 布局。

## 检查安装

检查已安装的版本，并验证一条简单陈述：

```bash
litex -version
litex -e '1 = 1'
```

这两条命令只检查可执行文件，不会使用标准库。下面描述的是当前源码版本的输出；旧安装版的选项和 JSON 字段可能不同。

`-version` 打印一行简短文本。默认英文模式下，`-e` 返回一份 Normal JSON `run` 文档；成功的批量检查以 `0` 退出，且包含 `"run_result": "success"`、`"session_terminated": false` 和 `"termination": null`。程序若需要英文 JSON 键，请使用 `-lang en`；`-lang zh` 会将这些键本地化。

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

应以 `0` 退出，并包含 `"kind": "run"`、`"run_result": "success"`、`"session_terminated": false` 和 `"termination": null`。若返回 `"session_terminated": true` 且 `termination.phase == "import"`，请先检查随包的 std 中是否有 `basics/litex.config`，以及二进制和 std 是否来自同一版本；若设置过 `LITEX_STD_PATH`，也请检查或取消该覆盖路径。

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
