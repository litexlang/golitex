<a id="litex-cli"></a>

# Litex CLI

<!-- CLI 主线：选择命令 → 运行 → 阅读 Normal JSON（或 REPL 文本） -->

这是当前 Litex 流水线（`src/`）的命令行参考。如果尚未安装 Litex，请先阅读简短的[安装指南](setup_zh.md)。

由沈嘉辰创建和维护。

在线阅读：https://litexlang.com/doc/cli

Markdown 源码：https://github.com/litexlang/golitex/blob/main/docs/cli.md

> **Litex 是一个仍处于 beta 阶段的实验性业余项目，使用中可能遇到不完善之处。**

<a id="before-you-start"></a>

## 开始之前

安装 Litex、检查安装或选择对应平台的安装包，请使用简短的[安装指南](setup_zh.md)。免本地安装试用，请使用[在线 playground](https://litexlang.com)。

<a id="first-run"></a>

## 第一次运行

启动 REPL：

```bash
litex
```

REPL 在 `cwd/litex.config` 存在时挂载该配置（否则使用空项目），然后接收交互输入块。没有末尾冒号的单行会立即运行；缩进块用空行结束。输入 `exit`、`quit`、`:quit` 或结束输入即可退出。成功的块打印 `success`。验证失败会打印包含原始语句和失败原因的 Normal JSON，然后接收下一个块。会话硬错误会停止 REPL，并报告一次。在续接的 `-session` 中，最终 JSON 保留初始批量运行的语句结果，并加入硬错误。交互式解析/分词错误引用 `<repl>`。

运行 `.lit` 文件：

```bash
litex -f "your_file.lit"
```

如果文件的直接父目录包含 `litex.config`，Litex 会挂载该模块，并运行配置中直到该文件为止的前缀（见[项目模块](#project-modules)）。否则独立运行文件。两种形式都是批量运行：输出一份 Normal `run` JSON 文档后退出。

直接运行 Litex 源码：

```bash
litex -e "1 + 1 = 2"
```

显示已安装版本：

```bash
litex -version
```

<a id="basic-shape"></a>

## 基本形式

```text
litex [-strict] [-session] [-lang <en|zh|zh-hant|fr|ru|es|ar|ja|ko|vi>] <command>
```

没有命令时，`litex` 启动上述交互式 REPL。

命令操作数之外的公共选项可放在命令之前或之后：

| 选项 | 含义 |
|------|---------|
| `-strict` | 禁止用户 `trust`、`trust have` 和 `axiom`；允许抽象谓词声明和命名基础规则的释放。 |
| `-session` | `-e` / `-f` / `-r` 成功后，保持 Runtime 打开并继续进入 REPL。 |
| `-lang <tok>` | JSON 验证反馈的输出语言：`en`（默认）、`zh`、`zh-hant`、`fr`、`ru`、`es`、`ar`、`ja`、`ko` 或 `vi`。不改变 Litex 源码或验证。 |

示例：

```bash
litex -strict -e "1 = 1"
litex -strict -e '-2 < 0'
litex -session -f chapter.lit
litex -lang zh -f examples/claim_obtain_scope.lit
litex -lang fr -e '1 + 1 = 2'
litex -f examples/claim_obtain_scope.lit
```

参数解析器采用小型白名单。不支持的选项和多余尾部 token 会被拒绝。`-strict -e "1 = 1"` 和 `-e "1 = 1" -strict` 都可使用。源码字符串应加引号，作为一个参数传入。shell 会移除引号；紧跟 `-e` 或内联提取命令的 argv 项会作为源码消费，即使它以减号开头或恰好与选项拼写相同。`-f` / `-r` 后的下一项同样是路径，即使以 `-` 开头。提取命令后紧接的 `-f` / `-r` 选择文件/仓库输入，随后一项为路径。例如 `-e '-strict'` 会把 `-strict` 传给 Litex 解析器并因源码无效而失败；它不会启用严格模式或启动 REPL。

当前白名单不包含 `-compact`、`-detailed`、`-runner`、`-before`、`-isolated`、`-factgraph` 或 `-defgraph`。这些旧命令写法不是本版本的入口。Rust 投影 API 与 CLI 选项相互独立。

`-strict` 在执行时拒绝用户 `trust`、`trust have` 和 `axiom`，包括嵌套证明语句与导入依赖。允许 `abstract_prop` 声明：它只引入谓词签名，不引入已证明实例。调用仍要求参数合法、元数准确并有证明。命名的集合论基础规则释放仍被允许。严格导入绕过缓存环境，以相同策略重新执行依赖源码。见[信任边界](Manual.md#trust-and-strict-mode)。

<a id="commands"></a>

## 命令

| 命令 | 行为 |
|---------|----------|
| `litex` | 挂载存在的 `cwd/litex.config`，然后启动交互式 REPL。 |
| `litex -e <code>` | 挂载存在的 `cwd/litex.config`，然后运行源码字符串。 |
| `litex -f <file>` | 挂载存在的 `parent(file)/litex.config`；否则独立运行文件。 |
| `litex -r <directory>` | 要求 `<directory>/litex.config` 存在，挂载全部导入，然后运行全部导出。 |
| `litex -lean -f <file>` | 验证独立文件，将受支持的带类型结果重放成 Lean 源码，写到标准输出（预览）。 |
| `litex -extractpython <code\|-f\|-r>` | 验证可提取片段，然后输出 Python `extracted_code` 产物（实验性）。 |
| `litex -extractc <code\|-f\|-r>` | 同上，输出 C99 片段（实验性）。 |
| `litex -help` | 打印用法文本。 |
| `litex -version` | 打印 `Litex <version>`。 |

`-extractpython` / `-extractc` 不接受 `-session` 或 `-strict`。使用 `-f` 时，源码必须包含成对的 `# [-extract]` / `# [end of -extract]` 标记；只有这些块会被验证和翻译。内联源码和 `-r` 对整个输入处理。详见 [`src/extract_executable_code/README.md`](../src/extract_executable_code/README.md)。

源码与路径操作数必须是下一项 argv，且不能为空。`litex -e '-2 < 0'` 和 `litex -extractpython '-2 < 0'` 都合法。所有 argv 项必须是合法 UTF-8；无效字节产生启动错误，以 `2` 退出。`-lang` 选择 JSON 键与解释语言；用法文本、REPL 提示符与 `success` 反馈仍为英文。

启动与挂载细节见 [`src/run/README.md`](../src/run/README.md) 和 [`src/module_manager/README.md`](../src/module_manager/README.md)。

<a id="statement-outcomes"></a>

## 语句结果

内部每条语句有三种结束方式：

| 内部结果 | 含义 | 父环境 | 会话 |
|----------|---------|------------|---------|
| **Success** | 语句完成 | 临时环境合并到父环境 | 继续 |
| **Failed** | 软失败（搜索 / WD 等） | 丢弃临时环境 | **继续** |
| **SessionError** | 硬失败 | 不合并 | **停止** |

批量 JSON 将这些结果呈现为：

| 内部结果 | Normal JSON 中的形式 |
|----------|----------------|
| Success | 语句 `"success": true`；当全部语句成功且没有会话错误时，运行也为 `"success": true` |
| Failed | `statement_results` **内部**的语句 `"success": false`（展示可能称为“error”；Rust 内部仍是 Failed） |
| SessionError | 顶层 `"session_error"` 被设置；会话必须停止 |

软失败语句留在 `statement_results` 中，**不会**被提升为清空该数组的顶层 `verify_error`。只要出现 Failed 或 SessionError，进程退出码就是非零。

软失败不证明命题为假。它表示当前路线未能建立该命题（或良定义性检查失败）。应补充更小的事实、修复定义域义务或修正语句。

<a id="json-output-contract"></a>

## JSON 输出契约

`-e`、`-f` 和 `-r` 的批量结果在标准输出上产生一份 Normal `run` 文档。分词、解析和早期 I/O 失败也产生带 `session_error` 的失败 Normal 文档。无效命令行形式仍在标准错误上产生文本，并以 `2` 退出，因为没有选定命令。提取失败产生带 `error` 的失败产物文档。成功与失败产物共用 `format`、`target`、`path`、`output_path` 和 `language`，字段名遵循 `-lang`。成功的 `-session` 在打印批量 JSON 前进入文本 REPL，因此它的标准输出不是一个独立 JSON 值。

投影定义见 [`src/json_output/README.md`](../src/json_output/README.md)。它**不会**转储完整 verify/exec IR；该树仍可供 Rust Detailed 投影与其他工具使用。下游读取方关闭标准输出时，Litex 保留命令的退出状态，不会 panic。其他输出 I/O 错误会正常报告。

<a id="run-envelope"></a>

### 运行封装

```json
{
  "kind": "run",
  "success": true,
  "target": "eval",
  "path": null,
  "detail": "normal",
  "language": "en",
  "statement_results": [],
  "session_error": null
}
```

| 字段 | 含义 |
|-------|---------|
| `kind` | 验证器批量命令始终为 `"run"` |
| `success` | 当且仅当全部语句成功且 `session_error` 为 null 时为 `true` |
| `target` | `"eval"`、`"file"` 或 `"repo"` |
| `path` | `-e` 为 `null`；`-f` / `-r` 为请求的路径 |
| `detail` | 默认 CLI 投影为 `"normal"` |
| `language` | `-lang` 选定的语言：`"en"`、`"zh"`、`"zh-hant"`、`"fr"`、`"ru"`、`"es"`、`"ar"`、`"ja"`、`"ko"` 或 `"vi"`（默认 `"en"`）；非英文输出也会本地化已知键 |
| `statement_results` | 按顺序排列的 `-e` / 目标 `-f` 语句；当前 `-r` 摘要让数组保持为空 |
| `session_error` | 硬停止载荷，或 `null` |

程序应读取 `success`、`statement_results` 和 `session_error`。退出状态 `0` 表示批量成功；`1` 表示运行失败或解析/I/O 错误；`2` 表示返回给启动器的无效参数错误。以会话错误捕获的无效语句属于运行失败，以 `1` 退出。机器消费者应使用 `-lang en`，要求退出码为 `0`，解析 JSON 并要求 `kind == "run"`、`success == true`、`session_error == null`。当前封装没有 `ok` 字段。`-r` 根据各文件计算整体成功，但不把它们的语句数组序列化进摘要。需要目标文件的语句解释时使用 `-f`。

`statement` 以可读形式保留完整的已解析源码，包括定理/公理名称、定理参数和选定结论。计算或发布的事实放在 `stores`。对于 `1 / 0 = 0`，失败语句仍为 `1 / 0 = 0`；`why_failed.phase` 为 `well_defined`，消息说明无法证明良定义性。这是证明失败，不是在断言每个未证明的表达式都在数学上无定义。

<a id="custom-indexes-and-visualizations"></a>

### 自定义索引与可视化

保存普通文件输出，供下游工具使用：

```bash
litex -lang en -f example.lit > result.json
```

利用 `statement_results` 中的成功项，从 `statement` 读取声明和定理调用，从 `stores` 与 `infers` 读取已接受的数学事实。`proof_method` 提供摘要，部分验证路线还带可读引用。这些字段支持自定义索引和可视化，无需单独的图输出格式。

Normal JSON 不包含每个验证子节点或 FactId 引用，因此不能保证重建完整依赖图。Rust Detailed 投影暴露更多带类型的证明证据；它是 API，而不是 CLI 选项。`-r` 的 Normal 摘要中 `statement_results` 为空；每个目标文件的语句输出应使用 `-f`。失败文件中的成功语句项，不代表该文件已作为完整导出发布。

<a id="chinese-output"></a>

### 中文输出

`litex -lang zh -e "1 = 1"` 会本地化封装键、语句键和证明解释。`run`、`eval`、`normal` 等类似枚举的封装值仍为英文：

```json
{
  "种类": "run",
  "成功": true,
  "目标": "eval",
  "路径": null,
  "详细度": "normal",
  "语言": "zh",
  "语句结果": [
    {
      "成功": true,
      "语句": "1 = 1",
      "证明方法": {
        "类型": "内置规则",
        "规则名": "由内部表示相等",
        "说明": "两边具有相同的内部表示"
      },
      "存储": [
        "1 = 1"
      ],
      "推断": []
    }
  ],
  "会话错误": null
}
```

<a id="normal-statement-shape"></a>

### Normal 语句结构

成功：

```json
{
  "success": true,
  "statement": "0 <= k",
  "proof_method": {
    "type": "known_atomic_fact",
    "cite": "0 <= k"
  },
  "stores": ["0 <= k"],
  "infers": []
}
```

软失败（仍在 `statement_results` 内部）：

```json
{
  "success": false,
  "statement": "a > 10",
  "why_failed": {
    "phase": "search_proof",
    "goal": "a > 10"
  },
  "stores": [],
  "infers": []
}
```

规则：

- `success` 是布尔值，而不是 `outcome` 字符串。
- `stores`、`infers`、`cite`、`statement` 和 `goal` 使用可读 Litex 文本。
- 内置解释使用 `rule_name` 和 `message`，不用旧的 `rule` 标签。
- Normal 省略良定义性子树；语句不成功时查看 `why_failed.phase`。

<a id="examples"></a>

### 示例

成功的内联运行：

```json
{
  "detail": "normal",
  "kind": "run",
  "language": "en",
  "success": true,
  "path": null,
  "session_error": null,
  "statement_results": [
    {
      "infers": [],
      "statement": "1 = 1",
      "stores": ["1 = 1"],
      "success": true,
      "proof_method": {
        "type": "builtin_rule",
        "rule_name": "Equal by IR",
        "message": "Both sides share the same internal representation"
      }
    }
  ],
  "target": "eval"
}
```

保留成功前缀的软失败：

```json
{
  "detail": "normal",
  "kind": "run",
  "language": "en",
  "success": false,
  "path": null,
  "session_error": null,
  "statement_results": [
    {
      "infers": [],
      "statement": "have a R",
      "stores": ["a $in R"],
      "success": true,
      "proof_method": { "type": "define_obj" }
    },
    {
      "infers": [],
      "statement": "a > 10",
      "stores": [],
      "success": false,
      "why_failed": {
        "goal": "a > 10",
        "phase": "search_proof"
      }
    }
  ],
  "target": "eval"
}
```

<a id="help-and-version"></a>

### 帮助与版本

`litex -help` 打印纯文本用法。`litex -version` 打印 `Litex <version>`。无效参数组合在标准错误上打印简短的 `launch_error: ...` 行，以 `2` 退出。

<a id="session-flag"></a>

## 会话选项

`-session` 不是独立的分帧协议。它表示：`-e`、`-f` 或 `-r` **成功**运行后，保留最后的 Runtime 环境，继续进入普通 REPL。失败的批量运行不会进入该 REPL。

示例：

```bash
litex -session -f chapter.lit
```

<a id="project-modules"></a>

## 项目模块

没有 `submodule`，也没有 `[hierarchy]`。`[export]` 只列出 `.lit` 文件。`[import]` / `[import std]` 在同一个共享别名命名空间下挂载模块（`[import std]` 中单独的 `N` 表示 `N = N`；`Alias = StdName` 解析为 `<std_root>/<StdName>`）。

夹具：[`examples/module_manager/`](../examples/module_manager/)。

用 `litex.config` 组织模块：

- 在 `[export]` 下按数学顺序选择参与的 `.lit` 文件，每个只出现一次（只允许文件，不允许导出子文件夹）；
- 用 `[import] Alias = path` 声明外部模块目录；在 `[import std]` 下用单独的 `N` 或 `Alias = StdName` 声明标准库包；
- 两个导入区段中的别名应保持全局唯一；
- 用规范名称引用挂载包与导出，例如 `Algebra::chap1::name` 或 `basics:::name`。

`[export]` 是显式选择列表，不是目录清单。未列出的文件是附属文件：发现阶段不解析或执行它们。文件和 REPL 中都拒绝源码级 `import`；项目源码使用清单。普通运行可以加载匹配的 `__litex_knowledge_base__/` 缓存；未命中时，Litex 执行导入导出项，并尝试回写缓存。严格运行始终执行导入源码导出项，而不重放缓存。根导出遵循下述执行顺序。

<a id="mount-behavior"></a>

### 挂载行为

| 命令 | 配置查找 | 挂载行为 |
|---------|---------------|----------------|
| `litex -r <dir>` | `<dir>/litex.config`（必需） | 全部导入，然后全部导出 |
| `litex -f <file>` | `parent(file)/litex.config`（缺失时为空） | 已列出：导入及直到该文件的导出；未列出：全部导出，然后该文件；无配置：独立运行 |
| `litex -e <code>` | `cwd/litex.config`（缺失时为空） | 全部导入和全部导出，然后 eval |
| 直接 `litex` | `cwd/litex.config`（缺失时为空） | 全部导入和全部导出，然后 REPL |

挂载时的软 Failed 会转为会话 `FailToImport`。对于 `-f`，**目标文件本身**的软 Failed 是普通文件失败，不是 `FailToImport`。

<a id="lean-compiler-boundary"></a>

## Lean 编译器边界

`litex -lean -f <file>` 是普通 `litex` 二进制的一种预览输出模式。它完整验证独立文件一次，然后消费胜出的带类型结果、对象 WD 和带作用域的引用。成功时只将 Lean 源码写到标准输出。验证失败或编译不支持时返回非零，将诊断写到标准错误，不输出部分 Lean 产物。

```sh
litex -strict -lean -f lean/examples/real_is_complex/statement.lit
```

当前数值切片覆盖自反性、集合性、字面量的 N/Z/R/C 成员关系、普通 forall 引入、数值层级桥接，以及带闭合整数幂的已认证加/减/乘/取负/除法对象。选定的 Rational 规范化使用显式指称传递和固定 Lean 规范化器；带保护条件的路线消费记录的非零证明。算术构造器合同性、精确闭合计算子节点和标量除法关系也重放各自选定的证据。支持仍取决于实际证明路线和对象定义域；即使另一个 Core 定理能证明结论，不支持的路线仍失败。这个首批切片不支持会话、仓库模式、其他输出模式和模块配置/导入。

最终产物是 [lean/Litex.lean](../lean/Litex.lean) 和 [lean/examples/](../lean/examples/)，每组源码/生成文件对各有一个问题目录。开发工具与计划仅限本地，位于 `scripts/litex_to_lean/`；旧资料留在 `scripts/legacy_to_lean/`。输出源码不同于 Lean 内核检查，数值模型也尚未解释整个 Litex。空的 `Rational {}` 结果标签记录的是规范化类别成功，不是单项式推导：生成的规范化证明必须通过 Lean。

声明切片加入 let 和带类型右侧 have 别名、命名定理及显式定理选择。相等类路径、受支持的参数传递和整个 forall 的复用保留精确的记录引用。有界原子改写支持整个参数别名与已认证的闭合代表元。选定的闭合数值等式子树代换保留精确引用及残余证明。数值支持范围包含 Q 的层级/封闭性、实数比较、有界弱序规则，以及作为一般参数上下文并有实际非空性检查的普通顶层数值 have。局部任意 have 证明步骤、函数/集合构造器、一般不等式求解、细化载体和未编译的前向推导类别仍在当前范围之外。

<a id="practical-recipes"></a>

## 实用命令

```bash
litex -e "1 = 1"
litex -f examples/claim_obtain_scope.lit
litex -r examples/module_manager/repo
litex -strict -f examples/claim_obtain_scope.lit
litex -session -f examples/claim_obtain_scope.lit
```

<a id="latex-conversion-preview"></a>

## LaTeX 转换（预览）

`litex -latex -lang zh -e '1 = 1'` 将已解析源码编译为 LaTeX 产物。`-f <file>` 选择独立文件或已注册项目中直到该文件的前缀；`-r <project>` 按清单顺序转换根导出。依赖清单提供名称；依赖源码不会被执行或输出。

使用 `-latex -document` 生成完整 XeLaTeX article，省略 `-document` 则生成片段。十种 `-lang` 选项都选择完整的数学叙述模板。JSON 键在不同语言下保持稳定；`content` 包含 LaTeX，`success` 报告转换结果，`verified` 始终为 false。转换失败时 `content` 为 null，进程以 1 退出。无效启动参数通过公共参数解析器产生标准错误，并以 2 退出。转换不执行或验证源码；`-strict` 和 `-session` 被拒绝。保存 `.tex`、字体/宏包要求、API 与覆盖范围见[编译器指南](../src/compile_to_latex/README.md)。

内部的 `CompileToLatex` 和 `ExtractExecutableCode` 是不同启动命令，也有不同结果类型。`-latex` 经过普通命令分派器；它不共用 C/Python 的验证与可执行代码提取流水线。
