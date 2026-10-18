<div align="center">
  <img src="../assets/logo.PNG" alt="Litex logo" width="300">

# Litex

### 写数学。看见它为何成立。

**读音：** Litex 读作 /ˈliːtɛk/（“里泰克”），不是“赖泰克”。

由沈嘉辰创建和维护。

_“Language is an instrument of human reason, and not merely a medium for the expression of thought.”_

_— George Boole, The Laws of Thought (1854), Chapter II (excerpt)_

[English README](../README.md) ·
[官网](https://litexlang.com) ·
[阅读中文蓝图](Litex中文蓝图.md) ·
[Read the Blueprint](Litex_Blueprint.md)
</div>

## Litex 的目标

为什么同一个数学证明，写成形式化证明时的感受，常常与写在纸上如此不同？Litex 探索的是一个语言设计问题：

**如果围绕日常数学写作来设计，一门形式化证明语言应该是什么样的？**

Litex 希望在自然语言的表达自由与形式化验证的严格性之间搭起桥梁，让数学家沿着熟悉的方式发展定义与论证，同时把假设、条件与推理表达得足够精确，使机器能够检查。

**Litex 走“正常数学”的路线：保留通常教科书中的数学含义与定义域条件。** Lean/Mathlib 的标准实数除法满足 [`(1 : ℝ) / 0 = 0`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/GroupWithZero/Basic.html#div_zero)。Litex 则要求先建立 `x != 0`，才接受 `1 / x`；`1 / 0 = 0` 会因表达式没有定义而被拒绝。这是运算语义的主动选择，Lean 同样能表达受限定义域。除法、减法与实数平方根的具体对照见 [Lean–Litex 示例](Lean与Litex示例对比.md#ordinary-mathematics)。

一门新数学语言的意义，在于帮助各个分支的数学家共同推进工作，加深对数学的认识与理解。Litex 的长期愿景，是让表达想法、审阅证明、继承彼此的知识拥有一门共同的语言。[蓝图](Litex中文蓝图.md#goal-of-litex)进一步展开了这一目标。

## 写下一条事实，看它留下了什么

Litex 是一门人类可读、基于集合论、面向事实、可编译到 Lean 的形式化语言。

**Litex 很适合与 AI 交互：** AI 提出数学步骤，Litex 检查并返回反馈，AI 在同一 Session 中基于已接受的知识修正或继续。

直接写下下一条数学事实；Litex 会检查它，并展示找到的依据，或指出检查停在何处。

```litex
1 + 1 = 2
have a R = 2
a + 1 = 3
```

第一行由计算检查。第二行引入实数 `a`：Litex 记录 `a $in R` 与 `a = 2`。随后用已有事实检查 `a + 1 = 3`，并把该等式存入后续可用的上下文。作者决定要建立什么；Litex 搜索局部可支持的依据，并报告所用方法。

> **写或修复 Litex 代码时，请打开 `-session` 并保持该进程。普通失败的语句会保留此前已接受的定义和事实。不要每加几行就从头重跑整个文件。** 见[下方简短对照](#与人和-ai-通过反馈协作)。

定义也进入同一流程：

```litex
prop is_odd(x Z):
    x % 2 = 1

$is_odd(3)
```

Litex 通过定义检查具体断言，并把 `$is_odd(3)` 留在当前上下文。这些是事实导向界面的小例子，并不表示验证器能从最终陈述自动发明整份证明。

**Litex 如何工作。** 见 [Litex 验证流水线](https://litexlang.com/assets/diagrams/litex-verification-pipeline-v1.png)，直观了解检查事实、寻找局部依据，以及把已接受知识提供给后续步骤的过程。

**多语言反馈。** CLI 可用多种语言呈现 JSON 验证反馈。同一源码可用 `-lang zh` 得到中文说明，或用 `-lang fr` 得到法文说明。得益于 AI 辅助翻译，多语言说明文案变得可行；语言设置只改变反馈，不改变被检查的数学陈述。见 [CLI 语言选项](Litex命令行参考.md#basic-shape)。

**给工具用的数学内容。** `litex -lang en -f example.lit` 输出含语句文本、已存事实、推断事实与证明摘要的 JSON，可用于自建索引或可视化。普通 JSON 总结验证过程，不暴露全部依赖；见 [JSON 输出契约](Litex命令行参考.md#json-output-contract)。

**LaTeX 导出（预览）。** `litex -latex -document -lang zh -f example.lit` 将解析后的源码编译为数学 LaTeX，说明文可用十种 CLI 语言之一。它保留定义与显式证明步骤，但不执行或验证。见 [LaTeX 编译器指南](../src/compile_to_latex/README.md)。

## 从熟悉的数学对象开始

Litex 追求 Python 式的形式化数学入口，让更多人能学会构建可检查的知识。

Litex 以集合论（ZFC）为数学基础，把集合、元素、函数与关系作为工作词汇。在 `have a R = 2` 中，隶属与相等是语言可再次使用的事实；作者不必先为 `a` 选择抽象载体类型。函数定义域、集合隶属及其他良定义条件，仍须在陈述被接受前检查。

```litex
have S set = {x R: x > 0}
have fn square(x R) R = x^2
square(2) = 4

prop is_less(x, y R):
    x < y

$is_less(2, 4)
```

**符号输入。** Litex 也接受熟悉的数学符号：`s ∩ u ⊆ t ∩ u` 是
`intersect(s, u) $subset intersect(t, u)` 的符号写法。
多数例子使用字母拼写，因为在普通键盘上更容易输入。见[支持的 Unicode 别名](Litex手册.md#unicode-mathematical-input-aliases-preview)。

Lean 把证明精化到依赖类型论核心；其可执行程序的编译器 IR 是另一条路径。Litex 把集合隶属与事实作为默认书写层。Lean 也能表达集合论；这里比较的是默认界面，不是当前覆盖范围。

Litex 源码的简洁，来自对象、事实、语句与验证过程之间经长期迭代形成的协调。它把连接常见证明步骤的机械工作纳入语言的默认检查，让作者直接陈述数学步骤，并建立在已有知识之上。蓝图中的[系统工程视角](Litex中文蓝图.md#systems-engineering)用一个小的互惠函数贯穿这一设计。

## 让已检查知识生长

_“If I have seen further it is by standing on the shoulders of Giants.”_

_— Isaac Newton, letter to Robert Hooke (1676)_

每条被接受的陈述，都会扩展后续陈述可用的数学上下文。

```litex
prop is_positive(n R):
    exist a R+ st {n > a}

claim:
    ? forall x R:
        x > 10
        =>:
            $is_positive(x)
    witness exist a R+ st {x > a} from 10

have a R:
    a > 10

$is_positive(a)
```

蓝图中的[已检查 Cantor 例子](Litex中文蓝图.md#overview-spine)走得更远：定义对角子集，无 `trust` 证明一般定理，再应用到 `singleton` 函数，得到 `missing != singleton(0)`。

## 与人和 AI 通过反馈协作

人选择问题、构造与数学含义。AI 可以直接陈述下一条数学事实。Litex 检查它；结构化反馈标出被拒语句的阶段与目标。活的 `-session` 在 AI 修复候选或提出下一步时，保留已接受的定义与事实。这些机制支持反复的
**提出 → 检查 → 读反馈 → 修正 → 继续** 交互。

外部写作工具可以保存尝试与反馈供日后审阅；完整协作记录由该工具负责。

[![Litex Agent 流水线：AI 提出 Litex 步骤，验证器返回 JSON 反馈，已接受事实累积为已检查源码。](../assets/litex-agent-pipeline.png)](../assets/litex-agent-pipeline.png)

*AI 提出，Litex 检查，已接受知识累积。输出预览示意已检查源码的可能用途。*

**在一个 Session 中保留已接受上下文。** 从一条已检查声明开始：

```bash
litex -lang zh -session -e 'have a R = 2'
```

在同一进程中输入后续每条语句。失败 JSON 从略：

```text
litex> a = 3
{"run_result": "failure", ..., "session_terminated": false, "termination": null}
litex> a + 1 = 3
success
```

失败的 `a = 3` 不会去掉已接受的 `a = 2`。下一条计算立刻使用它，无需重复声明。对 AI 作者，拒绝信息提供 `why_failed.phase: "search_proof"` 与
`why_failed.goal: "a = 3"`：可据此检查停点，在保留已接受上下文的同时提出可支持的下一步。

对比两条独立命令：

```bash
litex -lang zh -e 'have a R = 2'
litex -lang zh -e 'a + 1 = 3'
```

第一条成功；第二条失败，因为新进程没有 `a` 的声明。从头开始需要重新加载已接受代码。对已有通过文件，用 `litex -session -f accepted-prefix.lit`，再逐条提交新的顶层语句。在连贯检查点或结束时保存已接受源码并另做干净文件检查。仅在进程停止或必须更换已加载上下文时才重启并重放；精确边界见[智能体指南](Litex智能体指南.md)。

**Session 复用对依赖推理至关重要。** 若有 `N` 个依赖步骤、每步验证约耗时 `t`，一个 Session 约耗时 `Nt`。每步都重检完整前缀的成本是
`t(1 + 2 + … + N) = tN(N + 1) / 2`。在每步成本相同、每步只提交一次且前提不变时，累计时间比约为 `(N + 1) / 2`：二次相对线性增长。该模型不含初始加载、单独检查点/最终检查，以及必须的重启/重放。

<a id="independent-lean-rechecking-is-a-goal"></a>

## 对受支持数学子集做独立 Lean 复核

Litex 用自身验证器检查受支持源码。预览命令 `litex -lean -f <独立文件>` 把受支持的类型化结果重放到 Lean 源码。[`lean/Litex.lean`](../lean/Litex.lean) 拥有语义接口，[`lean/examples/`](../lean/examples/) 含问题相关的源码/生成对。生成与 Lean 内核检查是分开的门禁；当前编译器配置不覆盖完整 Litex 系统。开发材料与早期编译器仅在被忽略的 `scripts/` 下本地可用。见蓝图的 [Lean 一节](Litex中文蓝图.md#compatibility)。

浏览[源码/生成示例集](../lean/examples/)，从精确算术与带守卫的函数，到有界集合、定理复用与有理逆映射。文档记载的 2026-10-12 检查点用真实 Lean/Mathlib 检查了 74 对。编译器指南提供[五例阅读路径](Litex到Lean编译器指南.md#explore-the-example-collection)，每对都有两个文件的直接链接，便于同时查看数学与已实现的翻译。

<table>
<thead><tr><th>Litex</th><th>Lean（手写）</th></tr></thead>
<tbody>
<tr>
<td valign="top"><pre><code>forall s, t, u set:
    s $subset t
    =&gt;:
        intersect(s, u) $subset intersect(t, u)</code></pre></td>
<td valign="top"><pre><code>import Mathlib
example {α : Type*} (s t u : Set α) (h : s ⊆ t) :
    s ∩ u ⊆ t ∩ u := by
  intro x hx
  exact ⟨h hx.1, hx.2⟩</code></pre></td>
</tr>
</tbody>
</table>

Litex 是实验性 beta 项目。其内置与推断规则，以及用户书写的 `trust` 或 `axiom`，都属于当前信任边界。成功的 Litex 检查应在此范围内理解；[手册的信任与严格模式一节](Litex手册.md#trust-and-strict-mode)说明如何处理假设。`-strict` 拒绝已执行的用户 `trust`、`trust have` 与 `axiom`（含导入依赖）；抽象谓词签名与命名基础发布仍允许。

## 试用 Litex

在[在线 playground](https://litexlang.com) 运行，或在 macOS / Linux 上用 Homebrew 安装：

```bash
brew install litexlang/tap/litex
litex -e '1 + 1 = 2'
litex -lang zh -e '1 + 1 = 2'
litex -e '∅ ∩ ℕ ⊆ ℕ'
```

其他平台与检出构建见[安装指南](安装Litex.md)。浏览[showcase 索引](../showcases/README.md)，可见数学讲座、教材改编、证明教程、问题、理论库与功能演示。[命令行参考](Litex命令行参考.md)说明命令与验证输出；[手册](Litex手册.md)与[示例](../examples/README.md)是继续书写 Litex 的起点。[Linear Algebra in Litex](../showcases/linear_algebra/README.md) 是紧凑的数学入门。[Tao Analysis 章节发展](../showcases/analysis/README.md) 是对第 1–8 章选段的更大、非严格改编；它明确给出四条用户公理、一个抽象谓词与省略分支。完整论证与更多源码例子见[蓝图](Litex_Blueprint.md)与[中文蓝图](Litex中文蓝图.md)。

要理解实现，请按[源码阅读指南](../src/README.md)：先从中心数据结构开始，再跟踪检查语句并扩展数学上下文的组件算法。

更多中文文档见[中文文档索引](中文文档索引.md)。

## 关于

_“The best way to predict the future is to invent it.”_

_— Alan Kay, “The Early History of Smalltalk” (1993)_

沈嘉辰（Jiachen Shen），Litex 的创建者，是复旦大学数学博士生。Lean 向他展示了数学与编程可以在真实语言中相遇；Litex 探索形式化源码能否更贴近人们构造数学论证的方式。

蓝图描述 Litex 的[数学价值观](Litex中文蓝图.md#mathematical-values)（[English](Litex_Blueprint.md#mathematical-values)）。

特别感谢 Wei Lin、Siqi Sun、Peng Sun、Chenxuan Huang、Yan Lu、Sheng Xu、Keyao Zhu 与 Zhaoxuan Hong 的支持与建议。

Litex 以 [Apache License 2.0](../LICENSE) 发布。

## 项目主张、交付与证据

下表列出已实现功能，以及各自的例子与检查记录。

| 当前主张 | 实现 | 例子与检查记录 | 范围 |
| --- | --- | --- | --- |
| 作者可直接陈述数学事实，并由系统检查受支持的连接。 | 对象、事实、定义、良定义检查与局部验证过程。 | [源码示例](../examples/README.md)、[语言手册](Litex手册.md)与[实现指南](../src/README.md)。 | 已实现的数学界面与证明路径，受[已文档化的信任边界](Litex手册.md#trust-boundary)约束。 |
| 已接受知识可支持后续数学工作。 | 保留的事实、可复用定义与定理、引用与模块。 | [知识复用](Litex中文蓝图.md#workflow-reuse)与[数学发展](../showcases/README.md)。 | 在各声明的前提、作用域与导入规则下复用；各发展自行标明假设与检查状态。 |
| 人与智能体可在保留此前已接受上下文的同时修复一步。 | 持久 Session、结构化失败反馈与 JSON 结果。 | [可执行 Session 演示](../examples/agent_session_demo/README.md)与 [JSON 契约](Litex命令行参考.md#json-output-contract)。 | 已演示的交互与上下文保留行为。其对写作时间与证明质量的影响需另测。 |
| 界定的数学子集可编译到 Lean、独立复核，并通过原生 Mathlib 界面使用。 | 类型化结果重放、Lean 语义核心、生成源码对与手写适配器。 | [覆盖与示例地图](Litex到Lean编译器指南.md#current-mathematical-coverage-and-examples)、[源码/生成对](../lean/examples/)与[完整 Adapter 例子](examples/litex_to_lean/add_zero/README.md)。 | 已审阅路径与注明日期的 Lean 检查。2026-10-12 检查点覆盖 74 对；原生使用还依赖该界面的已检查模型与适配器。 |
| 数学源码与结果可供给其他工具。 | JSON 输出、LaTeX 导出与实验性 Python/C 提取。 | [JSON 输出](Litex命令行参考.md#json-output-contract)、[LaTeX 导出](../src/compile_to_latex/README.md)与[计算例子](Litex中文蓝图.md#workflow-use)。 | 各工具支持的输入输出契约。LaTeX 导出渲染解析源码但不验证；可执行提取处理受支持的计算片段。 |

设计依据见蓝图的
[主张、交付与证据](Litex中文蓝图.md#claims-deliverables-evidence)
（[English](Litex_Blueprint.md#claims-deliverables-evidence)）。

## 致读者

我们热烈欢迎对 Litex 做压力测试——难证明、边界情形与真实数学工作，是看清何物成立、何处仍需打磨的最好方式。项目尚小，人力与资源有限，部分表面仍未完成或较粗糙。希望读者以耐心对待这些地方，分享建设性反馈，并在工作成熟过程中彼此支持——而不是把每一处不成熟细节都当作针对其余部分的扣分项。
