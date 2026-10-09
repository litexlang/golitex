# 安装 Litex

Litex 是一个处于 beta 阶段的实验性业余项目，使用中可能遇到不完善之处。

如果希望免安装试用 Litex，可以使用[在线 playground](https://litexlang.com)。

## 安装

官方安装包同时包含 `litex` 可执行文件和标准库。所有发行版本都可以在 [GitHub Releases 页面](https://github.com/litexlang/golitex/releases)找到。

### macOS 和 Linux：使用 Homebrew

```bash
brew install litexlang/tap/litex
```

当前 macOS 的 Homebrew 安装包面向 Apple Silicon。Linux 提供 `amd64` 和 `arm64` 安装包。

### Ubuntu 和 Debian

从[最新发行版](https://github.com/litexlang/golitex/releases/latest)下载与你的架构（`amd64` 或 `arm64`）匹配的 `.deb`，然后安装：

```bash
sudo dpkg -i litex_<version>_<architecture>.deb
```

### Windows：使用 Scoop

在 PowerShell 中运行：

```powershell
scoop bucket add litex https://github.com/litexlang/scoop-litex
scoop install litex
```

如果不用 Scoop，可以从[最新发行版](https://github.com/litexlang/golitex/releases/latest)下载 Windows `amd64` 压缩包，同时解压 `litex.exe` 和 `std`，并把它们所在的目录添加到用户的 `Path`。

## 检查安装

检查已安装的版本，并验证一条简单陈述：

```bash
litex -version
litex -e '1 = 1'
```

`-version` 打印一行简短文本。默认英文模式下，`-e` 返回一份 Normal JSON `run` 文档；成功的批量检查以 `0` 退出，且包含 `"success": true` 和 `"session_error": null`。程序若需要英文 JSON 键，请使用 `-lang en`；`-lang zh` 会将这些键本地化。

如果要检查当前检出的源码，而不是另行安装的发行版：

```bash
cargo build --release
./target/release/litex -version
./target/release/litex -e '1 = 1'
```

参考文档描述的是当前检出版本的 `src/` 入口。已安装发行版的命令集可能不同，请对照 `-version` 和 `-help`。

## 入门命令

```bash
litex                              # start the interactive REPL
litex -e '1 + 1 = 2'               # run source directly
litex -f example.lit               # run a project file or standalone file
```

上面三条命令依次启动交互式 REPL、直接运行源码，以及运行项目文件或独立文件。完整的命令、选项、JSON 输出结构、会话选项和项目布局规则，见[完整 CLI 参考](cli_zh.md)。接下来可尝试的短证明，见[示例](../examples/README.md)。
