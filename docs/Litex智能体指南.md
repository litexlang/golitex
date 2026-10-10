<a id="litex-agent-guide"></a>

# Litex 智能体指南

> **修复证明时，保持同一个活动 Session。普通语句失败不会清除该会话中已经接受的定义和事实。修正失败语句，再提交给同一个进程。**

Litex 逐条语句构建数学上下文。复用上下文既保留先前证明工作，也保留加载章节或模块依赖所付出的成本。重启会创建新上下文；仅编辑源文件不会更新正在运行的进程。

<a id="see-why-keeping-the-session-matters"></a>

## 为什么保留 Session 很重要

这个有意构造的教学例子使用不透明谓词，让算术不能自动证明结果。`ready_at_seven` 是显式教学假设，不是数学定理的证明。绝不能只为让真实失败证明通过而添加公理。

在没有 `litex.config` 的目录中启动：

```bash
litex -lang en -session -e 'abstract_prop ready(n)'
```

在**同一个进程中，每次输入一条**以下语句。记录中的失败 JSON 被缩略；验收记录保留完整输出。

```text
litex> axiom ready_at_seven:
...     ? forall n N:
...         n = 7
...         =>:
...             $ready(n)
...
success
litex> $ready(8)
{"success": false, ..., "session_error": null}
litex> $ready(7)
success
```

最后一次成功使用第一条语句存储的事实。失败的 `$ready(8)` 不会清除 `$ready(7)`，也不会成为存储事实。再次尝试 `$ready(8)` 仍失败。如果重启时只加载相同的 `abstract_prop ready(n)` 声明，`$ready(7)` 也失败：新进程有谓词签名，却没有旧进程的公理。重放已接受语句才能恢复缺失上下文。

明确展示新进程对照：再次启动同一命令，再逐条分别输入：

```text
litex> $ready(7)
{"success": false, ..., "session_error": null}
litex> axiom ready_at_seven:
...     ? forall n N:
...         n = 7
...         =>:
...             $ready(n)
...
success
litex> $ready(7)
success
```

额外重放就是重启带来的工作。普通候选失败后保留活动 Session；保存日志，以便不可避免的重启能恢复已接受前缀。失败候选本身不属于该前缀。

实际比较如下：

| 候选失败之后 | 下一次尝试 |
| --- | --- |
| 保留同一 Session | 先前已接受的定义和事实立即可用。 |
| 启动新 Session | 继续前须重新加载模块上下文，并重放已接受前缀。 |

长篇教材前缀与这一条已存储事实具有相同的行为。示例展示上下文保留；不测量速度提升，也不确立自动证明发现能力。

<a id="use-the-session-as-the-proof-writing-loop"></a>

## 用 Session 进行证明书写循环

1. 理解目标数学，查看已有内置、库和模块接口。一次加载所需上下文。
2. 按源码顺序，每次提交一条顶层语句。`claim` 或定理及其完整嵌套证明构成一条语句。发送下一候选前读完响应；多行输入用空行结束。
3. 收到 `success` 时，记录已接受源码并继续。普通失败若有 `session_error: null` 且重新出现 `litex>` 提示符，应保持进程并修复当前语句。失败表示缺少证明或良定义性证据，不是命题否定的证明。
4. 在连贯的检查点保存已接受代码，另行运行干净文件检查。交互上下文不能替代可复现文件。

**事务边界是语句，而不是整段粘贴输入。** 失败语句丢弃自身暂存的解析绑定与执行状态。先前成功语句保留。如果一个输入帧包含多条顶层语句，即使整帧 `success` 为 false，成功语句也可以提交；软失败不会阻止后续语句。不要假定整个候选片段都已回滚，也不要盲目重新提交已经提交的名称。在活动进程之外记录已接受前缀，使其可在重启或中断后恢复。

<a id="start-in-the-intended-context"></a>

## 在预期上下文中开始

使用检出版本的 [CLI 契约](Litex命令行参考.md)。开发检出版本用 `cargo build --release` 构建，使用 `target/release/litex`。

```bash
target/release/litex -lang en -f accepted-prefix.lit -session
```

`-f` 在进入 REPL 前执行目标，包括按顺序注册的、直到目标为止的导出。初始运行必须成功；`-session` 不跳过失败的草稿文件。处理未完成的已注册文件时，使用任务专属的临时模块，保留精确的前置导入/导出并设置空目标，然后按顺序提交目标语句。临时配置应位于正式模块之外，保留原导出顺序。

当前 CLI 没有 `-before`、`-runner` 或 `-compact`；不要复制这些历史写法，也不要引入字面的 `try:` 包装。当前运行时已处理每条语句的提交/丢弃边界。

<a id="restart-deliberately-and-restore-the-prefix"></a>

## 有意重启并恢复前缀

进程退出或不能接收输入、已加载模块前缀必须改变，或替换同名的已提交声明需要新上下文时，才重启。普通证明搜索失败不是重启条件。解析/分词错误和会话硬错误可以终止 REPL；已停止进程不能为下一次尝试保留可用上下文。

有意切换到经过验证的重建 Litex 可执行文件时，先保存已接受源码，再重启并重放。替换磁盘上的二进制不会更新已经运行的进程。仅构建或普通证明搜索失败，本身不是丢弃活动 Session 的理由。

记录错误，重新打开预期模块上下文，按顺序重放日志中的已接受语句，确认成功后再重试待处理语句。意外会话终止应记入所属源码的阻塞说明。不要声称上下文能在进程退出后保留，或任意内部错误都能就地恢复。

<a id="verify-the-saved-artifact-and-find-the-right-reference"></a>

## 验证保存的产物并找到参考

使用干净的 `target/release/litex -lang en -f <file>` 检查。要求退出码为 0，解析 JSON 后有 `kind: run`、`success: true` 和 `session_error: null`。需要排除用户公理和 trust 时使用 `-strict`；上述教学公理在严格模式下会被有意拒绝。`-r` 留给显式要求的整模块检查。见 [CLI 输出](Litex命令行参考.md#json-output-contract)。

| 需要 | 阅读 |
| --- | --- |
| 语言、定义域、证明命令与数学写法 | [手册](Litex手册.md) |
| 入门书写选择 | [学习速查表](Litex学习速查表.md) |
| 短小可运行示例及其假设 | [示例](../examples/README.md) |
| 模块接口与章节依赖 | 所属模块的 `README.md`、`math_collections.md` 和 `litex.config` |
| 仓库授权与仅限本地的边界 | [AGENTS.md](../AGENTS.md) 和适用的仓库策略技能 |

已验证示例与对照：2026-10-07 验收记录（已停用的历史任务记录）。显式的新进程重放也用当前工作树 release 构建重新检查过：复检验收记录（已停用的历史任务记录）。检查覆盖同进程保留、新进程拒绝、失败复合语句回滚、混合帧逐语句提交、硬错误终止以及公理的严格模式拒绝。它们不改变内核语义，也不提出 agent 性能结论。
