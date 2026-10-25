<div align="center">
  <img src="../assets/logo.PNG" alt="Litex logo" width="300">

# Litex

### Write math, get formalized code: because the math already is.

**读音：** Litex 读作 /ˈliːtɛk/（“里泰克”），不是“赖泰克”。

由沈嘉辰创建和维护。

[English README](../README.md) ·
[官网](https://litexlang.com) ·
[Litex 中文蓝图](Litex中文蓝图.md)
</div>

<a id="litex-的目标"></a>

## 数学本身能不能就是形式化语言？

从小我们就知道，数学是一种严格的语言：引入对象，给出定义，陈述事实，并为每一步找到依据。我开始构建 Litex，就是出于一个问题：**能不能让这些数学直接被机器检查，只添加足够使含义精确的结构和约束？**

在 Litex 中，下面就是一段完整的形式化源码：

```litex
1 + 1 = 2
```

检查器直接读取这条数学陈述。复杂的论证还需要定义、条件和证明步骤，但目标始终一样：写下你要表达的数学，让语言检查其中的推理。

这个想法决定了 Litex 怎样构建：选什么数学对象和含义，怎样设计语法，怎样实现验证器，以及返回怎样的解释。下面这些选择，就是这样一步步长出来的。

<a id="familiar-mathematics"></a>
<a id="mathematical-objects"></a>

## 先决定要表达怎样的数学

第一个问题是语言的数学基础。我选择集合论：集合、元素、函数与关系，本来就是许多人从中学到工作都在使用的数学词汇。属于也是一条数学事实：`1 $in N` 和 `1 $in R`，说的是同一个数与不同集合的关系。

熟悉的符号，还应该带着熟悉的数学含义。看看这三个表达式：

| 表达式 | 通常的教科书约定 | Lean / Mathlib | Litex |
| --- | --- | --- | --- |
| 除以零 | `1 / 0` 没有定义。 | `(1 : ℝ) / 0 = 0` | 拒绝 `1 / 0 = 0`：分母必须非零。 |
| 自然数减去更大的数 | 在整数算术中，`1 - 2 = -1`。 | `(1 : Nat) - 2 = 0` | `1 - 2 = -1`，结果属于 `Z`。 |
| 负数的实数平方根 | `-1` 没有实数平方根。 | `Real.sqrt (-1) = 0` | 拒绝 `sqrt(-1) = 0`：输入必须非负。 |

Lean/Mathlib 对[除法](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/GroupWithZero/Basic.html#div_zero)、[自然数减法](https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/#Nat.sub)和[实数平方根](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Real/Sqrt.html#Real.sqrt_eq_zero_of_nonpos)有意采用了这些约定。在 Lean 中改用 `Int`，也有 `(1 : Int) - 2 = -1`。形式化检查器按照给定的定义检查；作者仍然需要知道，这些定义是否表达了原本想说的数学。

我希望 Litex 把通常的数学含义，以及使用它们需要满足的条件，放进默认的书写体验里。比如，倒数的非零条件就属于它的定义：

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

每次使用这个函数，都要检查 `x != 0`。要保留通常的除法含义，语言就需要检查它的定义域。

<a id="direct-facts"></a>

## 让数学陈述成为语法

数学词汇就位后，下一个问题是怎样写下来。Litex 用类似 Python 的缩进组织数学语句。“对任意两个非负实数，它们的和也是非负的”，可以写成：

```litex
forall x, y R:
    x >= 0
    y >= 0
    =>:
        x + y >= 0
```

先引入对象，再写前提，最后写结论。`=>:` 前是条件，后面的陈述需要被检查。

定义也用同样的数学词汇。把正实数收集成一个集合，再检查二属于它：

```litex
have positive_reals set = {x R: x > 0}
2 $in positive_reals
```

定义到原点的距离，建立非负性，再用它计算：

```litex
have fn distance_from_zero(x R) R = |x|

forall x R:
    distance_from_zero(x) = |x| >= 0

distance_from_zero(-3) = distance_from_zero(3) = 3
```

同样的写法可以延伸到集合之间的关系。下面两段代码都陈述了交集保持包含关系：

<table>
<thead><tr><th>Litex</th><th>Lean / Mathlib（手写）</th></tr></thead>
<tbody><tr>
<td valign="top"><pre><code>forall s, t, u set:
    s $subset t
    =&gt;:
        intersect(s, u) $subset intersect(t, u)</code></pre></td>
<td valign="top"><pre><code>import Mathlib
example {α : Type*} (s t u : Set α) (h : s ⊆ t) :
    s ∩ u ⊆ t ∩ u := by
  intro x hx
  exact ⟨h hx.1, hx.2⟩</code></pre></td>
</tr></tbody>
</table>

Litex 用内置的集合规则直接检查这个蕴含。结论也可以写成符号形式 `s ∩ u ⊆ t ∩ u`。语言使用有明确约束的形式化语法，让数学语句和源码尽量直接对应；符号输入见[记号指南](Litex手册.md#unicode-mathematical-input-aliases-preview)。

这个选择把“下一条数学事实”放到了证明书写的中心。右边展示的是 Lean 常见的 tactic 写法，Lean 也支持其他证明风格与自动化。较长的 Litex 论证仍然需要作者给出数学路线：中间事实、见证或分情形。验证器检查它支持的局部连接。

<a id="knowledge-workflow"></a>

## 围绕下一条事实构建验证器

要让这样的语法工作，验证器就需要回答：**给定当前的数学上下文，这条陈述凭什么成立？**

```litex
have a R = 2
a + 1 = 3
```

第一行引入 `a`，记录 `a $in R` 和 `a = 2`。第二行就能使用这些知识。检查通过后，`a + 1 = 3` 又成为后续步骤可用的事实。源码向下书写，数学上下文也随之生长。

我最早的实现思路很简单：匹配与代换。找到相关的已知事实，与当前陈述匹配，再检查代换和条件。它后来发展成结构化的事实查找、有界递归验证、内置数学规则，以及显式的证明步骤。

**把常见的数学表达一步步解析、组织成机器可识别、可存储、可调用的数学知识，是整个 Litex 项目的核心。** 难点在于让这条链路始终保留数学含义：识别陈述中的对象和事实，检查定义域与前提，保留作用域和成立依据，再让后续推理能够找到这些知识，并在满足条件时正确使用。

我把这里的存储与查找想成一个专为数学推理设计的数据库。它的设计必须和解析、表示、验证共同工作，让上一步建立的事实成为下一步能够使用的知识。直接书写数学的体验，就建立在这些环节协同工作的基础上。[源码阅读指南](../src/README.md)沿着 `a + 1 = 3` 展示了实际实现。

## 把检查依据放进输出

我还希望看见一句话为什么被接受，它建立了什么，以及失败的步骤停在哪里。回到 `1 + 1 = 2`，运行 `litex -lang en -e '1 + 1 = 2'` 会得到 JSON，其中这条陈述的结果是：

```json
{
  "statement_result": "accepted",
  "statement": "(1 + 1) = 2",
  "proof_method": {
    "type": "by_closed_calculation",
    "rule_name": "Closed calculation",
    "message": "Exact evaluation of closed expressions without proof search"
  },
  "stores": [
    "(1 + 1) = 2"
  ],
  "infers": []
}
```

源码陈述数学，输出报告检查方法、存入的事实，以及推断出的事实。这里的依据是一次精确的封闭表达式计算。换成 `1 / 0 = 0`，拒绝结果则会指出良定义性检查，以及无法满足的条件 `0 != 0`。

语法、语义和输出由此连在一起：我说了什么，它是什么意思，它凭什么能被接受？Normal JSON 是验证过程的摘要，完整依赖并不都在其中。[命令行参考](Litex命令行参考.md#json-output-contract)说明了输出契约；加上 `-lang zh` 等选项，也可以用中文等语言阅读反馈。

<a id="human-ai-feedback"></a>
<a id="work-with-people-and-ai-through-feedback"></a>
<a id="independent-lean-rechecking-is-a-goal"></a>
<a id="lean-rechecking"></a>

## 从验证记录继续往前走

当源码和检查结果一起留下来，就有了可以继续构建的东西。

人或 AI agent 可以提出一步，读取反馈，再修改。在同一个持久 `-session` 中，普通的拒绝会保留此前接受的知识：引入 `have a R = 2` 后，即使 `a = 3` 被拒绝，`a + 1 = 3` 仍然可以检查。书写时保持这个 Session；具体流程与重启边界见[智能体指南](Litex智能体指南.md)。我希望围绕这种交互构建一个有能力的数学 agent。

验证结果也提供了通往 Lean 的桥梁。实验性的 `litex -lean -f <独立文件>` 编译器，利用源码和类型化的验证结果，沿受支持的路线生成 Lean 陈述与证明。Lean 随后可以独立检查这些生成证明。可以对照阅读[源码与生成文件](../lean/examples/)，以及一个[完整的 Mathlib 适配例子](../showcases/litex_to_lean_adapter/README.md)。覆盖范围与忠实翻译，需要逐条路线建立；生成和 Lean 检查是两个步骤。[编译器指南](Litex到Lean编译器指南.md)说明了当前支持。

我也看到了用定义、事实和解释构建知识图谱、交互式数学教材的可能。这些是我希望继续探索的方向。现有工具已经提供 [JSON 输出](Litex命令行参考.md#json-output-contract)和 [LaTeX 导出](../src/compile_to_latex/README.md)；LaTeX 导出对解析后的源码排版，不执行验证。

## 试用 Litex

可以直接使用[在线 playground](https://litexlang.com)，或在 macOS / Linux 上用 Homebrew 安装：

```bash
brew install litexlang/tap/litex
litex -e '1 + 1 = 2'
```

其他平台与检出构建见[安装指南](安装Litex.md)。开始书写可以读[手册](Litex手册.md)与[短例子](../examples/README.md)，也可以从 [showcase 集合](../showcases/README.md)阅读一段数学发展。

Litex 仍是实验性 beta 项目。验证器、内置与推断规则、数学基础都属于当前信任基础；用户书写的 `trust` 和 `axiom` 会增加假设。`-strict` 拒绝已执行的用户假设，包括导入依赖中的假设，但仍保留固定数学基础。详见[信任与严格模式](Litex手册.md#trust-and-strict-mode)。

## 关于

我是沈嘉辰（Jiachen Shen），复旦大学数学博士生，也是 Litex 的创建者。Lean 让我看到数学与编程可以在真实语言中相遇；Litex 则来自我想继续探索的一件事：这样的语言，能在多大程度上贴近我们书写和理解数学的方式？

我通过建造自己能用的东西、检视它做了什么、让每个答案暴露下一个问题，来探索这些想法。我希望更多使用数学的人，也能书写、理解和贡献机器可检查的数学。

[蓝图](Litex中文蓝图.md)（[English](Litex_Blueprint.md)）讨论更广的项目方向与证据。欢迎带来难例、边界情形和建设性反馈。

特别感谢 Wei Lin、Siqi Sun、Peng Sun、Chenxuan Huang、Yan Lu、Sheng Xu、Keyao Zhu 与 Zhaoxuan Hong 的支持与建议。

Litex 以 [Apache License 2.0](../LICENSE) 发布。更多中文资料见[中文文档索引](中文文档索引.md)。
