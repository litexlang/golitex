# Litex：让数学自我验证的形式化语言

文档由沈嘉辰创建和维护。

最后更新：2026 年 9 月 30 日。

官网页面: https://litexlang.com/doc/Litex中文蓝图

英文版: https://litexlang.com/doc/Litex_Blueprint

> **Litex 是测试版（beta）的实验性爱好项目，可能存在边缘问题。** Litex 作者不是所谓的专家；蓝图中的观点没有权威性，欢迎讨论。

> **当前实现边界（2026-09-30）：** 本文区分设计目标与当前 `src/`。当前构建没有接入 Lean 编译入口；第 6 节保留的是早期实验与目标接口。带“迁移示例”说明的代码尚不能作为当前内核已验证的例子；运行命令和输出以 [CLI 文档](cli.md) 为准。

<!-- 蓝图主线：AI 带来的推理过剩 → 科学对象 → 设计假设 → 可测成本 → 潜在能力影响 → 验证与理解的双重瓶颈 → 两种参与门槛 → 四项语言设计 → 单条语句留下的知识记录 → Human–AI–Litex skill 与知识生产协议（含定义与验证） → 记录的重放、复用和 Lean/Mathlib 接续 → 生态角色 → 从 AI for Math 走向 AI 时代的可信高效推理 → 成功标准 -->

<!--
Litex 定位四层检查（写作时逐层核对；面向不同受众可以调整强调重点，但不能混淆层级）：
- 科学对象：可检查知识如何被表示和逐步构造。
- 科学假设：事实导向表示与事务式交互是否构成新的形式语言范式。
- 科学结果变量：这种范式怎样影响人类与 AI 构造、理解、审核、修复和复用知识的成本，以及单位时间内能够可靠处理的候选推理量。
- 社会影响：以 AI for Math 为起点，降低进入可验证知识生产与审核的门槛，使验证能力有可能跟上 AI 产生候选推理的速度，并为 AI 时代更广泛的可信高效推理积累方法与基础设施。
写作边界：前三层是 Litex 的科学内核；第四层是潜在影响。不得用“从而”把未验证的科学结果写成已经实现的工具效果。
-->

## 目录

- [0. Litex 蓝图总览](#overview)
  - [0.1 不同读者的入口](#overview-readers)
  - [0.2 五条主线](#overview-spine)
  - [0.2 源码速览（gallery）](#overview-gallery)
- [1. Litex 的数学基础：从最广为人熟悉的集合论出发](#set-theory)
- [2. 事实导向：把“什么成立”写进源码](#fact-oriented)
- [3. 自下而上：让已证明的事实推动后续证明](#bottom-up)
- [4. 每句话都留下什么：可检查知识记录](#execution-model)
- [5. 人类-AI-Litex 循环工作流构建](#interaction-loop)
- [6. Litex代码如何编译成Lean代码，并与Mathlib兼容（Experimental）](#compatibility)
  - [个人思考：Litex补齐了AI推理的范式缺口？](#summary-bottom-up-and-top-down)
- [7. 把证明编译成可执行代码（Python / C）（Experimental）](#executable-code)
- [8. 从语言到生态：Litex 想扮演什么角色](#ecosystem-role)
- [9. 追寻与众不同的艺术](#conclusions)
  - [特别感谢](#special-thanks)

<a id="overview"></a>

## 0. Litex 蓝图总览

*Litex (始于2024年) 是一门基于集合论的形式化语言，设计上追求易学易用。Litex源码按日常数学书写：用户直接写下对象与事实——想要证明什么；系统自下而上验证，并把每一步的成立依据或停止位置反馈出来。Lean 互操作是其设计目标，但当前构建尚未接入该编译器。由此，Litex 希望与人类、AI 一起形成协作闭环，为 Math for AI 积累可检查的验证工作。*

这背后，Litex 关心的是一个数学问题：形式化语言能否同时做到「好写好懂」与「可严格检查」——源码贴近自然数学表达，验证过程又能把每一步的作用和数学依赖摊开给人看。自然语言便于理解，却难以保证严格验证；形式化代码能够验证，却常常难以理解。Litex 希望成为二者的桥梁。

*一句话说：Litex 想做形式化语言里的 Python——让可检查数学更好学、更好写、更好读；并且读的时候；不只读到源码，还能读到源码背后的数学依据，加深对数学的理解并激发灵感；这样更多非专业人士也能掌握一门形式化语言，帮助到自己的工作。*

数学的价值在于帮助人类理解我们所处的世界。希望Litex能帮忙守住[促进理解](https://terrytao.wordpress.com/2026/09/11/a-severe-misalignment-of-ai-in-mathematics/)这一AI时代，人最容易失去、也最需要守住的东西。

<a id="overview-readers"></a>

### 0.1 Litex在不同场景下的价值投影和定位

下面不是互斥的用户分类，而是理解 Litex 的四种入口。您可以从最熟悉的问题进入，再回到后面的五条主线。

#### 写给 Lean 用户

为什么还要另一种形式化语言？

我第一次看到 Lean 时，十分震惊：数学居然可以写成代码，证明居然可以交给机器检查！“数学代码化”这个想法本身就让我感到兴奋，也让我开始思考自己希望怎样使用一门形式化语言。

学习过程中，我渐渐有了几个问题。What if，我能直接写下 `1 + 1 = 2`，不用先写 `example`，再接一个 `by ...`？What if，定义了奇数以后，我直接写 `$odd(13)`，语言就能按定义检查它？What if，已经知道“所有人都会死”和“苏格拉底是人”，我就能直接写“苏格拉底会死”，不用再点名引用那条全称前提？

这些问题逐渐汇成了 Litex 的一个基本想法：**用户写下数学的每一步，形式语言寻找并解释这一步为什么成立。** 计算、定义和已知前提提供了不同的依据，而用户始终可以用同一种方式参与：写下接下来应当成立的事实。

作者仍然负责关键的数学构造和推理路线；语言则尽可能承担步骤之间的局部验证，并把找到的依据呈现出来。Litex 的许多简化与约定，都围绕这个分工展开。

围绕这一分工，Litex 形成了几个基本出发点：

1. 用户侧回到集合、元素、函数与关系，而不是先穿越类型工程。
2. 源码默认写 *what to prove*，由内核检索 *how*。
3. 常用事实不必处处取名点名，并给出可读的 proof trace。
4. 语义足够直白时，应能编译到 Lean 等可表示集合论的系统，再由对方内核独立复核。

```text
Lean:  命题 → 证明目标 → tactic 精化 → 证明项 → 内核检查
Litex: 对象与事实 → 内核检查并检索依据 → 已验证事实扩展上下文
```

还有一层差别在 tactic 之下。Lean 的默认表面经由依赖类型论，把数学对象、命题、证明与类型收进同一套 term/type 宇宙——于是值与证据常常被打包在一起（如下方 subtype 示例）。Litex 在用户表面把这些范畴分开：对象、事实、语句各自独立，更贴近日常数学已经在用的说法。这不是关于证明能力的主张，而是关于源码首先让你看见什么。*Litex的“类型”系统更像是Python，Lean更像Rust*

以 Lean 为代表的现代形式化语言，为 AI for Math 和“数学的工程化”奠定了不可替代的基础。然而，无论 AI 如何发展，能够熟练掌握 Lean、类型论及其工程体系的人，仍可能只是少数。Litex 并非试图取代 Lean，而是探索另一种形式化视角：让更多人能够直接书写、检查和理解严格的数学知识。Litex 与 Lean 近乎「互反」的默认设计——一方源码偏 *how*、另一方源码偏 *what*、一方偏从条件出发积累结论、另一方偏化简结论直到匹配上条件——等于把形式化系统里原先大半藏在界面背后的那一面也翻出来；于是不同思维习惯的人，都能找到属于自己的那个语言。

*这里有一层常被低估、却很本质的分工：**语言帮你证，用户给出证什么**——而不是反过来让用户先学会怎么证、再把证明步骤写进源码。因此 Litex 的输出不只是“通过 / 失败”：它会告诉你每句话背后的数学依据。读 Litex 源码时，你既在读“要成立什么”，也能从输出里读到源代码以外、支撑这句话的数学原理。而Lean通常是反过来的，源码里写怎么证，Lean的输出告诉你你证明得到了什么。*

如果你想理解Litex的设计，最好是自己再走一遍这条路：从日常数学出发，发现界面错位，把 *what* 交还给人、把 *how* 交给内核。走完之后，你得到的未必叫 Litex；但你会明白它为何几乎不得不长成这样。

Lean 始终是 Litex 学习的参照。早期编译实验探索了把 Litex 的验证证据交给 Lean，仓库保留的产物展示了这条互操作路线。但当前 `src/` 和 Cargo 构建目标尚未接入该编译器。更易读的 Lean 前端是研究方向，不能据此宣称当前任意 Litex 程序都能编译成 Lean。

因为 Litex 替你搜索想要的 *how to verify*，这个搜索过程在设计上会较为复杂；同时 Litex 还必须内置常见的 verify rule。因此 Litex 整套需信任的验证与规则实现（可信实现面）约有二十余万行 Rust——可达 Lean 小内核（约 5–8 千行 C++）的几十倍。但运行时另一面也成立：Litex 不必先把证明编译成中间码再精化；本质更像一个巨大的、按形状做的 fancy Ctrl+F——在事实表与规则表里做受约束匹配。因此，典型交互路径上，搜索的时间与内存成本通常远低于 Lean 那套编译—精化—内核检查路径。这也是为什么 Litex 在 AI 时代之前几乎不可能完成：一门语言要成功，设计最好保持一致，作者人数最好不超过两人；但 Litex 系统过于巨大，一两人在没有 AI 帮助下根本无法完成这样的工程——何况形式化语言对 bug 近乎零容忍。正是因为可信实现面巨大，Litex 作者必须让 Litex 具备编译到 Lean 的编译器，才能借助 Lean 小内核独立复核，确保 Litex 内部运行没有问题。

<details>
<summary><strong>Lean–Litex 对照示例</strong></summary>

下面直接放三组代表性 Lean–Litex 对照代码。为保持表格简洁，Lean 示例省略了 `import` 行。它们比较的是默认接口，不是证明长短，也不声称两种语言的能力边界完全相同：

<table>
<thead>
<tr><th>Litex 示例</th><th>Lean 示例</th></tr>
</thead>
<tbody>
<tr>
<td><strong>直接事实：已知 x = 2</strong><pre><code>forall x R:
    x = 2
    =&gt;:
        x + 1 = 3
        x^2 = 4</code></pre></td>
<td><strong>同一事实</strong><pre><code>example (x : ℝ) (h : x = 2) :
    x + 1 = 3 ∧ x ^ 2 = 4 := by
  have h_add : x + 1 = 3 := by
    rw [h]
    norm_num
  have h_square : x ^ 2 = 4 := by
    rw [h]
    norm_num
  exact ⟨h_add, h_square⟩</code></pre></td>
</tr>
<tr>
<td><strong>带条件的函数定义域</strong><pre><code>forall x {y R: y &gt; 0}:
    x &gt; 0

have fn positive_successor(x R: x &gt; 0) R = x + 1

positive_successor(1) = 2</code></pre></td>
<td><strong>用 subtype 携带条件</strong><pre><code>def positiveSuccessor
    (x : {y : ℝ // y &gt; 0}) : ℝ := x.val + 1

example : positiveSuccessor ⟨1, by norm_num⟩ = 2 := by
  norm_num [positiveSuccessor]</code></pre></td>
</tr>
<tr>
<td><strong>交集保持子集关系</strong><pre><code>forall s, t, u set:
    s $subset t
    =&gt;:
        intersect(s, u) $subset intersect(t, u)</code></pre></td>
<td><strong>展开集合定义并逐点证明</strong><pre><code>example {alpha : Type*} (s t u : Set alpha) (h : s ⊆ t) :
    s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩</code></pre></td>
</tr>
</tbody>
</table>

</details>

<details>
<summary><strong>展开两个门槛例子</strong></summary>

下面两个例子展示复杂度税的两个来源。它们不比较数学能力，只追问：从“我明白”到“我能形式化”，还差什么？

1. **工具使用门槛**：用户已经理解一个数学事实，却未必知道怎样把它写进形式系统。
2. **表达方式门槛**：形式系统中的数学写法，可能与我们熟悉的日常数学表达不同。

先看工具门槛。很多时候，数学本身已经够简单——例如小朋友也会写的 `1 + 2 = 3`，或一条多项式恒等式——卡在形式系统里的，往往不是“懂不懂数学”，而是记不记得该调用哪个 tactic、哪条引理。

Litex：

```litex
1 + 2 = 3

forall a, b R:
    (a + b)^2 = a^2 + 2 * a * b + b^2
```

Lean：

```lean
import Mathlib

example : (1 : ℝ) + 2 = 3 := by norm_num

example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
```

Lean 版本很有用，却要求用户先知道：数值等式用 `norm_num`，多项式用 `ring`；更复杂时还要记住定理库里的事实名，并在源码里显式调用。这些名字和调用步骤不是数学事实本身，却常常占掉大量时间与精力。Litex 追问：用户理解事实后，能否直接写下它，由系统完成检查所需的工具工作——而不必先学会记忆、检索并点名调用那些依据？

再看表达门槛。我们的数学问题是，函数 `f` 只接受正实数，且已知 `x > 0`；我们想说明 `f(x)` 等于自身。Lean 的一种常见编码是：

```lean
example
    (f : {x : ℝ // x > 0} → ℝ)
    (x : ℝ) (hx : x > 0) :
    f ⟨x, hx⟩ = f ⟨x, hx⟩ := rfl
```

对应的 Litex 是：

```litex
forall f fn(t R: t > 0) R, x R:
    x > 0
    =>:
        f(x) = f(x)
```

Lean 用子类型（subtype）把值与其为正的证明绑定，因此调用时组合 `x` 与 `hx` 为 `⟨x, hx⟩`。设计精确通用，但读者须越过这层表示才能看到 `f(x)`。

Litex 仍检查 `x > 0`，但让它作为普通事实留在上下文中，源码仍写 `f(x)`。省去的是手工传递证据；对 `f(x)` 的良定义性检查由验证器替您完成。

> **用户写数学，系统寻找依据。** Litex 节约的，正是记忆与调用事实名、tactic 名的时间和精力：`1 + 2 = 3` 不必 `by norm_num`，多项式恒等式不必 `by ring`。条件足够时，验证器会帮您找到每段数学是如何证明的。这极大降低了从“我明白”到“我能形式化”的门槛。

目前 AI for Math 行业遇到的问题是：AI 可能生成通过 Lean 内核的代码，但实际命题少了条件、改变了量词或弱化了结论。Lean 内核没有出错；它正确检查了代码中的命题。错在形式陈述没有对齐数学意图。

理想状态下，Litex 用户关注对象、条件、事实和结论，Litex 提供局部可追踪的反馈。*理解领域却并非证明助手专家的人，也能参与形式化，并知道系统检查到了哪里。*

> **这是设计方向，不是对当前语言、标准库或编译器已经完备的声明。**

</details>

#### 写给数学从业者

如果您从事数学，您可能首先关心的不是又一种工具，而是数学理解和数学代表的传统价值观在 AI 时代如何被保留。

AI 正在带来“推理丰盈”：答案与证明可以大规模生成，却不自动可信、可解释，也不必然加深理解。正如[陶哲轩在 2026 年 ICM 公开讲演](https://www.youtube.com/watch?v=M0--ZH1lOzg)所说，数学的未来更需转向证明的验证、阐释与消化。更普遍的问题是：如何把 AI 生成的推理变成可检查、可理解、可复用的共同知识——这不只关乎数学，也关乎各行业的知识生产。

今天的数学圈并不平静：热点轮换很快，AI 让数学问题有时像「挖矿」一样被追逐。就在2026年9月，陶哲轩等25位菲尔兹奖得主警告：AI公司把“快速解题”当作数学进步指标，可能牺牲真正的理解、原创性、学术传承与归属规范，导致AI发展目标与数学共同体严重错位。[原文](https://terrytao.wordpress.com/2026/09/11/a-severe-misalignment-of-ai-in-mathematics/)

Litex 并不反对应用，也不否认数学需要落地；但我们更想大家重新认识到，数学首先是一种理解的活动。数学的价值，在于帮助人类更好地理解了世界。

Litex 想做的，正是在形式化验证与日常数学思维之间加一层可读的抽象：让您不必先成为证明助手专家，也能把「我理解了什么」清楚地写下来，交给机器检查，再看到检查过程和背后的数学结构。我们追求的不是更炫的工具，而是达到这样一种境界：任何人脑海里有会的数学，他都能很自然地用litex表达出来，从而加深对数学本身的认识。

这种简单，有一部分是范畴上的，不只是记号上的。日常数学书写里，一个数不是一条定理，一条定理也不是一个类型。Litex 把这个习惯留在表面上：对象、事实、语句分开，读一份源码更像读数学，而不是先学一种新的数学编码。这里说的是表达与阅读成本——不是说每个定理都因此更好证。

没有什么群体比数学家更清楚：一套好的符号系统有多本质。从阿拉伯数字到莱布尼茨记号，每一次符号或书写格式的更新，都极大促进了数学本身；近代的 LaTeX 也是让大家互相沟通更方便。Litex 想请教的，正是这种对书写表面的敏感——形式化语言的接口，是否也能更贴近数学家已经在用的那套心流与习惯。

科学史反复表明，从全新的出发点重新审视已有问题，往往能够推动原有领域发展，甚至孕育新的学科。进入 AI 时代，复杂问题不断涌现，人们也越来越需要可信、可扩展且可解释的推理。在这一过程中，形式化方法将扮演越来越重要的角色。因此，多一种像 Litex 这样的探索，本身就是有价值的。

历史上影响深远的理论，往往始于对问题本身的纯粹好奇，而非对短期回报的算计。Litex作者希望从语言这一最底层的技术栈，推动Math For AI学科的发展。老实说，他只是对这个事情感兴趣才去做的。希望这份蓝图，能激发您借助litex来体会数学之美的冲动。

#### 写给程序员

Litex 的设计初衷其实非常简单：正如 Fortran 和 C 抽象了部分汇编语言，让系统工程与科学计算变得更容易；Python 又进一步抽象了 C 的部分使用场景，让没有专业编程背景的人也能参与其中。随着编程语言越来越易学、易用，越来越多人成为程序员，计算机行业也由此不断拓展。

程序员本来就熟悉另一组对照：函数式偏 *what*（应当成立什么），命令式偏 *how*（一步步怎么改状态）。奇妙之处在这里：Lean 本身是函数式语言，但日常用 Lean 写数学——tactic 证明——读起来却常常像命令式的 *how*：每一行攻击当前目标、改写证明状态。Litex 把默认界面拉回 *what*：源码写下应当成立的对象与事实，由验证器去找 *how*。Lean 作为语言底层仍是函数式的；显得倒过来的，是默认的*数学书写表面*。

还有第二个拧劲，关于类型的*手感*。经典函数式语言如 Lisp 常常是动态类型的，灵活正是其方便之处的一部分。Lean 也是函数式的，但当你用它写数学——而不是写普通程序——类型纪律非常严格，书写表面更接近静态类型系统。Litex 更靠近另一极：只要数学上合理，同一对象可以属于多个集合，日常接口更像 Python——精神上偏动态。这是接口类比，不是声称 Litex 在编程语言意义上实现了动态类型系统。

如果您已经写过代码，还可以把 Litex 看成一门把数学范畴拆开的语言——就像普通程序把值、语句与类型拆开一样。Lean 的默认表面把对象、命题、证明与类型收进同一套依赖 term/type 宇宙——强大且统一，却也容易读成「一切都住在同一种编码里」。Litex 的用户表面分开对象、事实与语句；函数仍是对象上的操作，事实仍是「什么成立」的断言。验证器照样检查良定义性与依据；改变的是源码要求你在工作记忆里同时抓住什么。

```text
Lean 表面:  terms / types   （对象、命题、证明同宇宙）
Litex 表面: 对象 · 事实 · 语句

Lean（作为语言）: 函数式 / 声明式
Lean tactic 证明:  常读作命令式 how
Litex 源码:        声明式 what；验证器寻找 how

Lean（写数学时）:  严格类型手感  ≈ static
Litex:             多集合归属    ≈ dynamic（偏 Python）
```

可以把 Litex 与 Lean 的关系粗略理解成 C 与汇编：Lean 的 tactic 证明里，常要给事实取名并显式调用；这对大脑是负担——人通常记住的是证明的 pattern（形状），而不是事实名。汇编里大量代码在写内存地址；C 替你维护“变量名 ↔ 地址”的表。Litex 类似：它维护一张事实表与规则表，你直接写出要证明什么，内核按原子事实的谓词名为 key 做匹配与替换（详见第 2 节），而不必先记住乱乱的事实名。Lean 难以直接扩充成同一默认机制，也正因为其语言允许命题高度一等量化——第 2 节会说明这条边界。

也可以从对象接口再看一层：Litex 的用户可见层更接近集合论——同一对象可属于多个集合；Lean 的默认用户层更强调每个项落在一个确定类型下。Litex 希望在数学推理与形式化验证之间建立类似的抽象层，让用户不必被底层实现细节牵绊，而能够把注意力真正放在思考本身。

还有第二条程序员常关心的实验性编译路线：计算片段在 Litex 里检查过之后，可以尝试抽出可运行的 Python 或 C（第 7 节）——同样标明实验性，且范围很窄，不是整门语言的后端。

#### 写给其他知识领域的读者

在数学之外，Litex 希望用简单的语法表达对象、关系、条件与规则，再用清晰的验证反馈，邀请我们探索人类直觉、机器验证与数学知识之间的另一种表现形式。Litex 也希望探索形式化语言在真实知识工作中的入口：从 AI 安全、AI 输出可解释性、金融风控、精密软件工程，到物理、化学、医疗、法律和工程。

这些目前是探索方向，不是对相关行业已有支持的声明。欢迎更多非数学专业背景的工作者参与探索：在自己的行业中使用形式化工具，理解依据、发现冲突、预防错误。

<a id="overview-spine"></a>

### 0.2 五条主线：Litex是怎么工作的

**Litex 不只是为形式化专家而创造的工具，它的目标更是让更多人成为形式化专家，让 Math for AI 成为可能。**

全文沿五个相连的问题展开：用户看见什么，源码保存什么，推理如何积累，证明过程如何呈现，结果如何独立复核。

1. **集合论对象**：用户直接看见集合、元素、函数和关系，而不必先管理抽象的承载类型。
2. **事实中心**：源码记录“什么成立”；验证器按形状匹配内置规则、已知事实与定义，做受约束的匹配与替换，并检查良定义性。
3. **自下而上积累**：每个通过验证的事实都会进入上下文，供后续推理使用；这是默认的推理方向。
4. **可追溯的证明流**：系统整理并输出每句话的数学依据，以及从定义、前提到结论的前后依赖，使证明过程成为可阅读、可检查、可复用的结构化信息——读源码之外，还能读到背后原理；出错时指出失败发生在哪里。
5. **Lean 复核**：目标是提供独立检查路径；`lean/` 保留了早期实验产物，当前构建尚未接入其编译器。

<a id="overview-gallery"></a>

#### 源码速览（gallery）

下面几段不是教程，只展示「直接写要证的东西」在 Litex 里长什么样；后文各节再展开设计与边界。

最简单的等式：

```litex
1 + 1 = 2
```

多项式恒等式：

```litex
forall a, b R:
    (a + b)^2 = a^2 + 2 * a * b + b^2
```

集合事实：

```litex
forall s, t, u set:
    s $subset t
    =>:
        intersect(s, u) $subset intersect(t, u)
```

非负数相加仍非负：

```litex
forall x, y R:
    0 <= x
    0 <= y
    =>:
        0 <= x + y
```

定义域条件已知时的良定义调用：

```litex
forall f fn(t R: t > 0) R, x R:
    x > 0
    =>:
        f(x) = f(x)
```

谓词——先定义，再当作原子事实使用：

```litex
prop is_positive(x R):
    x > 0

forall a, b R:
    $is_positive(a)
    a = b
    =>:
        $is_positive(b)
```

已知全称事实，用来推出具体的原子事实：

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

存在量词——先见证，再从 `exist` 事实取出对象：

```litex
witness exist x R st {x = 0} from 0

obtain zero from exist x R st {x = 0}
zero = 0
```

定理——命名可复用结论，再按需引用（整除传递性）：

```litex
prop divides_by(d, n Z):
    exist k Z st {n = d * k}

thm divides_transitive:
    ? forall a, b, c Z:
        $divides_by(a, b)
        $divides_by(b, c)
        =>:
            $divides_by(a, c)
    obtain k from $divides_by(a, b)
    obtain m from $divides_by(b, c)
    c = b * m = (a * k) * m = a * (k * m)
    witness $divides_by(a, c) from k * m:
        c = a * (k * m)

witness $divides_by(2, 6) from 3
witness $divides_by(6, 30) from 5

by thm divides_transitive(2, 6, 30) => $divides_by(2, 30)
```

具名函数：

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

局部证明块 `claim`——写出沿途应当成立的等式，不必点名改写方向：

```litex
claim:
    ? forall a, b, c, d, g, f R:
        a * b = c * d
        g = f
        =>:
            a * (b * g) = c * (d * f)
    a * (b * g) = (a * b) * g = (c * d) * g = (c * d) * f = c * (d * f)
```

反证法——否定「每个实数都满足 `x^2 >= x`」：

> **迁移示例：** 当前 `src/` 检查停在 `by_contra` (`by contradiction`)；以下保留写法不算已验证结果。

<!-- litex:skip-test -->
```litex
by contra:
    ? not forall x R:
        x^2 >= x
    impossible 0.5^2 >= 0.5
```

分类讨论——穷尽分支，再在每个分支里关闭目标：

```litex
have fn k(x R) R by cases:
    case x = 2: 3
    case x != 2: 4

have x R

by cases:
    ? k(x) > 2
    case x = 2:
        k(x) = 3 > 2
    case x != 2:
        k(x) = 4 > 2
```

归纳法——前 `n` 个正奇数之和等于 `n^2`：

> **迁移示例：** 当前 `src/` 检查停在 `internal_bug: name n is already bound in an enclosing parse scope`；以下保留写法不算已验证结果。

<!-- litex:skip-test -->
```litex
have fn kth_odd(k Z) Z = 2 * k - 1

thm sum_first_odds:
    ? forall n Z:
        n >= 1
        =>:
            sum(1, n, kth_odd) = n^2
    by induc n from 1:
        ? sum(1, n, kth_odd) = n^2

        ? from n = 1:
            kth_odd(1) = 2 * 1 - 1 = 1
            sum(1, 1, kth_odd) = kth_odd(1) = 1 = 1^2

        ? induc:
            kth_odd(n + 1) = 2 * (n + 1) - 1
            sum(1, n + 1, kth_odd) = sum(1, n, kth_odd) + kth_odd(n + 1) = n^2 + (2 * (n + 1) - 1) = (n + 1)^2
```

结构体——群：载体上的运算、单位元、逆元，以及单位元唯一性：

```litex
struct Group<s nonempty_set>:
    mul fn(x, y s) s
    one s
    inv fn(x s) s
    <=>:
        forall x, y, z s:
            mul(mul(x, y), z) = mul(x, mul(y, z))
        forall x s:
            mul(x, one) = x
            mul(one, x) = x
            mul(inv(x), x) = one

forall s nonempty_set, G &Group<s>, identity s:
    forall a s:
        G.mul(identity, a) = a
        G.mul(a, identity) = a
    =>:
        identity = G.mul(G.one, identity) = G.one
```

模板——按参数族实例化定义，再用 `\name<args>` 取出：

> **迁移示例：** 当前 `src/` 检查停在 `search_proof` (`p.first = 1`)；以下保留写法不算已验证结果。

<!-- litex:skip-test -->
```litex
struct Triple<X set>:
    first X
    second X
    third X

template<X set>:
    have fn triple(a, b, c X) &Triple<X> = (a, b, c)

\triple<R>(1, 2, 3) = (1, 2, 3)

have p &Triple<R> = \triple<R>(1, 2, 3)
p.first = 1
```

一道简单应用题——当前解析器使用 ASCII 变量名，注释可以写中文：

```litex
# 妈妈年龄是小明年龄的 3 倍再加 4；小明 15 岁。妈妈几岁？
have xiaoming_age R = 15
let mom_age = 3 * xiaoming_age + 4
mom_age = 3 * 15 + 4 = 49
```

你写出数学步骤；Litex 检查每一步的衔接，并把通过的事实留在上下文里。

<a id="set-theory"></a>

## 1. Litex 的数学基础：从最广为人熟悉的集合论出发

形式化语言选择的公理体系直接决定了该语言的表达能力的边界和源代码风格。Litex 选择最广为人熟悉的集合论作为基础，避免了依赖类型论或其他公理体系的额外学习成本。它的对象是集合、元素、函数和关系；它的事实是成员关系、子集关系、交并集、函数应用和等式。

例如，若 `s` 包含在 `t` 中，那么二者分别与同一集合 `u` 取交集后，前者仍包含在后者中：

```litex
forall s, t, u set:
    s $subset t
    =>:
        intersect(s, u) $subset intersect(t, u)
```

可以看到，这样的写法和我们在日常数学中看到的集合论陈述非常接近。

下面是《Mathematics in Lean》集合论章节中的同一数学语句的 Lean 版本：

```lean
import Mathlib.Data.Set.Lattice

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩
end
```

Lean 先声明共同元素类型 `α : Type*`，再声明 `s`、`t`、`u : Set α`。这让定理可在任意元素类型上复用；`Type*` 还涉及类型的宇宙层级。

差异不在于“短代码更强”：Lean 也能用短证明或自动化完成它；这里刻意保留教材的展开路径。真正的区别是默认接口：Lean 先赋予集合类型论载体，再构造证明；Litex 直接识别和检查常见集合论事实。

> **集合论决定对象怎么长；不决定你每天从哪一层开始写。**

选集合论作基础，常被听成两件事——其实是两层误解。

<details>
<summary><strong>两层误解：不是“先学会集合论写法”，也不是“从 ZFC 从头砌砖”</strong></summary>

**误解 1：我不太熟集合论，就不会用∈、∪去表达群、拓扑空间、开集这类常见概念。**  
这首先是**词典问题**，不是先修一门集合论课程才能动手。日常数学里怎么说，Litex 里就应有对应的可读写法。例如群、拓扑空间（及其开集族）可以直接写成工作层接口，而不必先手搓底层编码：

```litex
# Group: carrier set, operation, identity, inverse, and the usual laws
struct Group<s nonempty_set>:
    mul fn(x, y s) s
    one s
    inv fn(x s) s
    <=>:
        forall x, y, z s:
            mul(mul(x, y), z) = mul(x, mul(y, z))
        forall x s:
            mul(x, one) = x
            mul(one, x) = x
            mul(inv(x), x) = one

# Topology: a space is its carrier together with a family of open sets
prop is_topological_space(X set, open_sets power_set(power_set(X))):
    {} $in open_sets
    X $in open_sets
    forall U, V open_sets:
        intersect(U, V) $in open_sets
    forall family power_set(power_set(X)):
        family $subset open_sets
        =>:
            family_union(family) $in open_sets
```

开集就是该族中的成员：在显式假设 `$is_topological_space(X, open_sets)` 下，写 `U open_sets` 即表示 `U` 开。下文还有群与 Lean 的对照；这里只说明「词典」长什么样。覆盖仍在扩展，不宣称已经穷尽一切常用概念。

**误解 2：既然基础是集合论，是不是每次都要从 ZFC 公理把分析、代数、拓扑重造一遍？那会不会太难？**  
这是**入口高度问题**。Litex 确实提供集合论／ZFC 一侧的公理与构造接口，需要做基础研究或往下钻时可以用。但日常使用并不强迫展开这些概念的具体集合论构造定义：对日常书写中常见的对象与结构，系统给出可检查的关系与使用面，让你在想要的抽象层直接操作，而不是先从公理砌到那一层。底层接口是出口与逃生梯，不是每天上班必经的楼梯。

更准确地说：Litex 的内置层关心的是对象、语句与事实之间**可检查的关系**，而不是选定某一种“真正的”具体构造定义。例如有理数 `Q`、实数 `R` 可以有多种集合论构造，函数也可以用不同的图编码来建模；内置接口不把其中某一种定为唯一定义，而直接给出成员、包含、函数定义域与值域行为等可操作的关系。需要某一种具体构造时，可以在源码中自行写出，或在必要时用 `trust` 标注兼容性假设。

因此：集合论规定了对象语言长什么样；**工作入口**仍由你选择——可以从群或拓扑这类工作层出发，也可以在需要时落到公理接口。上面的片段和下文的群对照示范的都是工作层写法；它们并不要求读者先完成一套从空集公理开始的构造。

</details>

<details>
<summary><strong>技术总结：类型判断与成员事实</strong></summary>

Lean 把数学组织成有类型的项：经过细化后，核心表达式由 `Γ ⊢ e : T` 形式的判断检查。冒号属于元语言层的类型判断，不是 Lean 对象语言中可与等式、序关系或定理事实并列累积的普通命题。表层重载和强制转换可以把相似写法细化成不同的核心项，但每个所得项都在一个确定类型下接受检查。

Litex 则把数学组织成对象与逐步增长的事实上下文。`e $in S` 是对象语言中的成员事实，与等式、序关系和其他谓词处于同一逻辑层。因此，同一对象可被证明属于多个无关或相互重叠的集合：成员关系是对象之间的关系，不是唯一内生赋值 `typeOf(e) = S`。

这不等于取消静态约束或推断。Litex 在接受表达式前仍会检查定义域、返回集合、结构字段和其他良定义性义务，并通过专用规则在证明中推出成员与载体事实。区别在于，这种推断向上下文增加 `e $in S` 一类事实，而不是推断一个决定对象身份的特权类型 `e : T`。

Lean的技术路线选择了 Dependent Type Theory（依赖类型论）作为基础。Litex 的技术路线选择了集合论作为基础。两者都能表达同样的数学，但在默认接口、源码风格和理解成本上有根本性差异。Lean选择了更抽象的数学公理体系，让它具备了通用的编程能力，也让它的小内核更小更容易被检验。Litex 的可信实现面（验证与规则系统）可达 Lean 小内核的几十倍，因此把证据交给 Lean 独立复核是一条目标路线；早期编译实验尚未接入当前构建。二者没有高下之分，只是不同的技术路线选择。

</details>

<a id="group-comparison"></a>

<details>
<summary><strong>小例子：同一数学对象在不同的公理体系下的定义</strong></summary>

当标准库未覆盖某个领域时，用户能否从少量共同概念搭建理论？集合、函数、关系和运算是跨领域共享语言，可让定义和定理沿自身数学依赖生长，而非先服从外部库的编码。这就是**数学理论的自举**。

成熟库当然能加速建设，但不应成为表达新领域的前置边界。下面两个群片段表达同一结构和单位元唯一性，却呈现不同的载体、运算与规律接口。

群由元素、二元运算、单位元和逆元组成，并满足结合律、单位律和逆元规律。若另一元素也对所有元素表现为单位元，它必与原单位元相同。

#### Lean：`Type` 上的记录类型（record）与柯里化函数

```lean
structure Group where
  Carrier : Type
  mul : Carrier → Carrier → Carrier
  one : Carrier
  inv : Carrier → Carrier
  mul_assoc : ∀ a b c : Carrier, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : Carrier, mul one a = a
  mul_one : ∀ a : Carrier, mul a one = a
  mul_left_inv : ∀ a : Carrier, mul (inv a) a = one

theorem one_unique
    (G : Group)
    (e : G.Carrier)
    (hleft : ∀ a : G.Carrier, G.mul e a = a)
    (hright : ∀ a : G.Carrier, G.mul a e = a) :
    e = G.one := by
  calc
    e = G.mul G.one e := (G.one_mul e).symm
    _ = G.one := hright G.one
```

Lean 用 `Carrier : Type` 指定元素类型，后面的运算和规律都依赖它。`Carrier → Carrier → Carrier` 是依次接收两个元素的柯里化二元函数；结合律和单位律则成为 `mul_assoc`、`one_mul` 等具名字段。这便于抽象和大型库复用，作者也须知道证明中调用哪个字段、等式朝哪个方向使用。上例显式调用了 `G.one_mul`。

#### Litex：集合上的运算与直接写下的结构事实

```litex
struct Group<s nonempty_set>:
    mul fn(x, y s) s
    one s
    inv fn(x s) s
    <=>:
        forall x, y, z s:
            mul(mul(x, y), z) = mul(x, mul(y, z))
        forall x s:
            mul(x, one) = x
            mul(one, x) = x
            mul(inv(x), x) = one

forall s nonempty_set, G &Group<s>, identity s:
    forall a s:
        G.mul(identity, a) = a
        G.mul(a, identity) = a
    =>:
        identity = G.mul(G.one, identity) = G.one
```

Litex 先绑定非空集合 `s`，再把群写成其上的结构。`mul fn(x, y s) s` 表示运算接收 `s` 中两个元素，结果仍在 `s` 中；群规律作为普通事实写在 `<=>:` 下。单位元唯一性随后直接写成等式链，由内核寻找单位律依据。长期使用的结果仍可命名为 `thm`，但局部事实不必都先变成需要记忆的接口。

`G.mul` 等字段路径按声明的结构载体检查，路径本身不会把群公理加入上下文。直接绑定 `G &Group<s>` 只自动打开一层；函数返回值或嵌套结构字段须用 `release struct def expression`，先验证结构归属再释放一层。后来单独得到的 `expression $in &Group<s>` 保持不透明。

Lean 当然也能脱离 Mathlib 自行定义群；这里比较的是默认体验，不是表达上限。“从头搭建”也不是无依赖：Litex 仍依赖内核、规则和标准库，外部库仍是重要加速器，只是不应成为表达边界。上文“两层误解”已说明：工作层写法不等于从 ZFC 砌砖；这里的群片段是入口高度的示范，不是基础课作业。

群只是小示范。更强的检验是：小团队能否为现有库覆盖不足的领域建立可读、可扩展且边界清楚的接口。未来几何等领域库应以带日期的源码、验证结果、`trust` 边界和真实复用说明进展，而非预先宣称成功。

</details>

<details>
<summary><strong>设计空间中的位置：集合论式的表述并非 Litex 首创</strong></summary>

[Mizar 的数学库](https://wiki.mizar.org/library/) 基于塔斯基–格罗滕迪克（Tarski–Grothendieck）集合论；
[Lean](https://lean-lang.org/doc/reference/latest/The-Type-System/) 和
[Rocq](https://rocq-prover.org/doc/V9.2.0/refman/language/core/index.html) 向用户展示依赖类型论内核；
[Isabelle/HOL](https://isabelle.in.tum.de/website-Isabelle2024/dist/library/Doc/Isar_Ref/HOL_Specific.html)
使用多态高阶逻辑。

Litex 面向用户的命题语言大体具有一阶逻辑风格：原子关系或具名谓词通过受限的经典逻辑形式和量词组织。它偏好规范事实形态，命题和证明不能作为普通一等值任意组合——因此也不允许 `forall p prop` 一类对命题的量化；第 2 节说明这如何使事实表能按谓词名索引。这只描述命题接口；验证器还会检查良定义性，并从定义、上下文和受支持规则中寻找依据。

在这个背景下，Litex 的问题更具体地落在面向用户的对象接口上：
一套小型、以成员关系为中心的集合论式表层，能否在不要求用户先管理类型
宇宙（universe）的前提下，覆盖有实质内容的数学？

</details>

<a id="fact-oriented"></a>

## 2. 事实导向：把“什么成立”写进源码

任何数学证明都由“证明什么”和“怎么证”组成。阅读数学时，我们的心流通常是：看到书里的一句话，脑海里反应一下这句话为什么对，如果这句话被确认是正确的了，我们就在脑海里记忆下来这句话用于后续的推理。

Litex做的相当于就是把我们脑海的心流在机器中实现了。*用户写“证明什么”，内核按形状去匹配并检查这句话为什么成立。*同时，Litex把已经证明好的事实存储下来。当用户输入下一个数学语句后，Litex会从上下文中寻找依据，检查良定义性，并返回验证结果或停止位置。

> **事实导向最核心的人机分工是：用户写“我要证明什么”，Litex 寻找“这条事实可以怎样被验证”。**

这不只是界面偏好，也是在节约一种真实成本：用户不必为每条常见等式先记住该点名哪个 tactic、哪条引理——例如数值计算不必手写 `norm_num`，多项式不必手写 `ring`。关键选择、见证和估计仍由作者写；具体规则与等式对齐由内核寻找、记录。Litex 由事实触发局部搜索；结果都须可检查：Litex按关系、参数结构和上下文寻找内置规则、全称事实、具体事实或等式；搜索受支持范围限制，并非自由猜测。

### Litex如何帮用户按事实形状寻找验证路径

Litex 验证一条事实时，并不是在“想出一个证明”。更接近的图像是：把当前目标拆成谓词和参数形状，再到上下文与规则表里做受约束查找——有点像按形状 Ctrl+F。检索时，原子事实的谓词名（如 `>=`、`$is_positive`、`$in`）就是事实表与规则表的 key；对上之后做实例化或替换，再检查前提是否齐备；对不上就停在当前目标。**本质是匹配与替换，不是自由推理。** 正因为不必先编译成中间码再精化，典型路径上时间与内存成本通常也远低于 Lean 那套编译—精化—内核检查路径——它更像一个巨大的 fancy Ctrl+F，而不是一个定理证明搜索引擎的全套编译流水线。

常见匹配对象有四类：

| 匹配什么 | 内核做什么 | 极小例子 |
| --- | --- | --- |
| **内置规则**（builtin） | 按谓词/参数形状筛选规则，再核对前提 | 已知 `x >= 0`、`y >= 0`，匹配“非负之和仍非负”，得到 `x + y >= 0` |
| **已知具体事实** | 在上下文中找到同形事实；必要时用等式对齐写法 | 已知 `$is_positive(a)` 与 `a = b`，匹配并替换得到 `$is_positive(b)` |
| **已知 `forall`** | 把目标形状对上全称事实，实例化参数并检查前提 | 已有 `forall x R: x > 1 => $is_positive(x)`，且 `b > 1`，匹配得到 `$is_positive(b)` |
| **定义**（def） | 把具名谓词与其定义体互相同形状匹配 | 已知 `a > 0`，匹配 `prop is_positive` 的定义，得到 `$is_positive(a)` |

```litex
prop is_positive(a R):
    a > 0

# 1) 匹配内置规则（builtin）
forall x, y R:
    0 <= x
    0 <= y
    =>:
        0 <= x + y

# 2) 匹配已知事实，再用等式替换
forall a, b R:
    $is_positive(a)
    a = b
    =>:
        $is_positive(b)

# 3) 匹配已知 forall（先存下这条全称；再由 b > 1 得到 $is_positive(b)）
forall x R:
    x > 1
    =>:
        x > 0
        $is_positive(x)

have b R:
    b > 1

$is_positive(b)

# 4) 匹配 prop is_positive 的定义
have a R:
    a > 0

$is_positive(a)
```

用户记住的是这些形状模式；内核维护事实表与规则表，替你完成点名与对齐。

<details>
<summary><strong>为什么 Litex 能维护事实表？Lean 能否扩充实现同一机制？</strong></summary>

有人会问：既然 Litex 能在内核里维护事实表，让用户不必手写 `by xxx` 一类 tactic，Lean 能否扩充一下也做到？答案是：**很困难**——难处不在工程量，而在语言允许什么进入量词。

Litex 在设计上就不允许写成 `forall p prop` 这类对命题本身的量化。每条原子事实都有可命名的谓词头；内核以该谓词名为 key，去事实表与规则表里检索潜在候选，再做形状匹配与替换。正因 key 固定，搜索才是受索引约束的局部查找，而不是在全体上下文上盲目试探；用户也才不必为每条常见依据手动点名。

一旦语言允许 `prop`——甚至 fact 本身——作为 `forall` 的参数出现，原子目标就不再保证有稳定的谓词名可作索引。候选集合失去固定 key，搜索空间就膨胀成几乎整个上下文乃至全体可表达命题。那时「维护一张可按形状检索的事实表」与「用户少写 tactic」就很难同时成立：要么退回显式点名，要么面对不可控的全局搜索。

这不是说 Lean 的自动化（如 `simp`、`grind`）无用，而是说：**默认靠谓词名索引的事实表，依赖的是「命题不可任意一等量化」这一语言边界**；在依赖类型论里命题与证明高度一等，正是这条边界被放开之处。Litex 用表达力上的约束，换来了可索引的事实上下文。

</details>

下面再用三组 Lean–Litex 对照，把其中几类匹配展开成完整界面对比。Lean 源码当然也包含陈述目标的 theorem statement，Litex 也允许显式指定定理和证明结构；差异在默认的注意力中心：

| 典型界面 | 源码主要呈现 | 交互输出主要呈现 |
| --- | --- | --- |
| Lean tactic proof | theorem statement 给出目标，tactic proof body 主要写 **how**：怎样改写、应用定理或关闭目标 | Infoview 显示 **what**：当前还需要证明什么 |
| Litex 事实导向证明 | 源码主要写 **what**：哪些对象、条件和事实应当成立 | 验证输出解释 **how**：事实因何被接受，或验证停在哪里 |

> **默认界面的镜像关系：Lean 的 tactic 源码主要写 how，Infoview 显示尚未完成的 what；Litex 源码主要写 what，Litex 输出解释验证器找到的 how。** 这是典型工作流的对比，不是对两种语言全部书写方式的绝对概括。

下面的 Litex JSON 是解释性输出的节选。它展示当前版本怎样记录验证路径；字段名称、嵌套结构和消息文字可能随 Litex 版本变化。

<details>
<summary><strong>例子 1：Lean 与 Litex 如何验证“两个非负实数之和仍然非负”</strong></summary>

**内置规则。** Litex 把目标拆成谓词与参数形状，据此筛选候选规则，再检查类型、前提和条件是否全部成立。

要证明的数学事实是：两个非负实数之和仍然非负。

**Lean 源码｜proof body 写 how**

```lean
import Mathlib

example (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) : x + y ≥ 0 := by
  exact add_nonneg hx hy
```

最后一行明确告诉 Lean 使用 `add_nonneg hx hy` 关闭目标。执行这一行之前，Infoview 显示的是尚待证明的 **what**：

**Lean Infoview｜显示 what**

```text
x y : ℝ
hx : x ≥ 0
hy : y ≥ 0
⊢ x + y ≥ 0
```

**Litex 源码｜直接写 what**

```litex
forall x, y R:
    0 <= x
    0 <= y
    =>:
        0 <= x + y
```

这条源码没有指定规则名称。目标 `0 <= x + y` 可拆成谓词 `>=` 与参数 `x + y`、`0`；内核据此筛选候选，匹配出两个非负前提，并继续检查类型和条件。

**Litex 输出｜解释 how**

```json
{
  "kind": "run",
  "success": true,
  "detail": "normal",
  "session_error": null,
  "statement_results": [
    {
      "success": true,
      "statement": "forall x, y R: /     0 <= x /     0 <= y /     =>: /         0 <= x + y",
      "proof_method": { "type": "..." },
      "stores": ["..."],
      "infers": []
    }
  ]
}
```

</details>

<details>
<summary><strong>例子 2：Lean 与 Litex 如何复用一条全称事实</strong></summary>

**用户提供的全称事实。** 已证明的 `forall` 事实会进入上下文；遇到同形目标时，Litex 匹配参数并检查实例化后的前提。

第二个数学事实是：若实数 `a > 10`，则存在一个正实数严格小于 `a`。前面建立的全称事实随后可直接用于具体的 `a`。

**Lean 源码｜proof body 写 how**

```lean
import Mathlib

def HasPositiveWitness (n : ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ n > a

theorem hasPositiveWitness_of_gt_ten (x : ℝ) (hx : x > 10) :
    HasPositiveWitness x := by
  refine ⟨10, by norm_num, ?_⟩
  exact hx

example (a : ℝ) (ha : a > 10) : HasPositiveWitness a := by
  exact hasPositiveWitness_of_gt_ten a ha
```

最后一行执行前，Infoview 给出当前 **what**；源码中的 `exact` 指定完成它的 **how**：

**Lean Infoview｜显示 what**

```text
a : ℝ
ha : a > 10
⊢ HasPositiveWitness a
```

**Litex 源码｜直接写 what**

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

这里 `prop` 给出可复用接口；`claim` 建立一条可实例化的全称事实。后面的 `have` 提供具体前提，最终源码只写 `$is_positive(a)`，没有再次写出怎样调用全称事实。

**Litex 输出｜解释 how**

```json
{
  "kind": "run",
  "success": true,
  "detail": "normal",
  "session_error": null,
  "statement_results": [
    {
      "success": true,
      "statement": "$is_positive(a)",
      "proof_method": { "type": "..." },
      "stores": ["..."],
      "infers": []
    }
  ]
}
```

</details>

<details>
<summary><strong>例子 3：Lean 与 Litex 如何沿等式运输一个具体事实</strong></summary>

**具体事实与已知等式。** Litex 也能从上下文中的具体事实出发，利用已知等式对齐写法不同但相等的参数。

第三个数学事实是：已知 `a` 为正且 `a = b`，推出 `b` 为正。这里需要借助等式把一个具体事实运输到另一个写法。

**Lean 源码｜proof body 写 how**

```lean
import Mathlib

def IsPositive (x : ℝ) : Prop :=
  x > 0

example (a b : ℝ) (ha : IsPositive a) (hab : a = b) : IsPositive b := by
  simpa [hab] using ha
```

执行 `simpa [hab] using ha` 之前，Infoview 只呈现当前 **what**：

**Lean Infoview｜显示 what**

```text
a b : ℝ
ha : IsPositive a
hab : a = b
⊢ IsPositive b
```

**Litex 源码｜直接写 what**

```litex
prop is_positive(x R):
    x > 0

forall a, b R:
    $is_positive(a)
    a = b
    =>:
        $is_positive(b)
```

Litex 源码保存前提和结论，没有写 `simpa` 或指定等式改写方向。验证器从上下文找到 `$is_positive(a)`，再利用 `a = b` 对齐参数。

**Litex 输出｜解释 how**

```json
{
  "kind": "run",
  "success": true,
  "detail": "normal",
  "session_error": null,
  "statement_results": [
    {
      "success": true,
      "statement": "forall a, b R: /     $is_positive(a) /     a = b /     =>: /         $is_positiv",
      "proof_method": { "type": "..." },
      "stores": ["..."],
      "infers": []
    }
  ]
}
```

</details>

<details>
<summary><strong>个人观察：命令式与声明式编程的类比</strong></summary>

同一层拧劲已在 §0.1「写给程序员」里说清：函数式偏 *what*、命令式偏 *how*；Lean 是函数式语言，但 tactic 证明常读作命令式 *how*，而 Litex 的默认数学表面回到 *what*。这里只保留类比本身：Lean 的每一行 tactic 像命令式语句一样改写当前 Goal；Litex 让作者写下应当成立的事实，由验证器去找 *how*。

</details>

<details>
<summary><strong>设计空间中的位置：寻找局部证明依据并非 Litex 独有</strong></summary>

[Lean `grind`](https://lean-lang.org/doc/reference/latest/The--grind--tactic/)、
[Rocq `auto`](https://rocq-prover.org/doc/master/refman/proofs/automatic-tactics/auto.html)
和 [Isabelle/Isar](https://isabelle.in.tum.de/doc/isar-ref.pdf) 通过显式证明指令（tactic）或
证明方法（proof method）提供局部自动化；[Mizar](https://mizar.uwb.edu.pl/project/mizman.pdf)
有空验证（empty justification）；
[ACL2](https://acl2.org/doc/index-seo.php?xkey=ACL2____DEFTHM) 可以在没有提示（hints）时
尝试证明定理事件（theorem event）；[Naproche](https://naproche.github.io/) 则用自动定理证明器
检查受控自然语言中的步骤。Litex 更具体地检验：普通数学陈述能否触发受当前上下文和规则限制的局部验证，并在通过后写回上下文、显示验证来源。

局部自动化可以叠加在多种内核之上；Litex 强调的是另一条路：用「禁止对 `prop` / fact 任意量化」换取按谓词名索引的事实表，使默认证明不必依赖显式 tactic 点名。这与上文“为什么 Litex 能维护事实表”同一设计边界。

</details>

<a id="bottom-up"></a>

## 3. 自下而上：让已证明的事实推动后续证明

数学中有两种思维模式：一个是从前提出发，积累出越来越多的中间结论，最后得到我们想要证明的结论；一个是从结果出发，把结果不断化简，直到我们可以用已知的前提来证明它。前者是自下而上（bottom-up），后者是自上而下（top-down）。

Litex 的工作原理是自下而上的：从已知条件推出新事实，源码陈述结果。每一个已经验证的事实都可以被后续的推理使用。

书写Litex的心流通常是追问：“从我们已有的事实出发，还能得到什么新的事实？”积累足够多知识后，我们就能逐步接近目标。即使最后我们没有得到想要的结论，我们的中间步骤也是宝贵的，也许能用在其他问题里。

Lean 的典型交互则向后、自上而下：先固定目标，再把它分解为由假设或定理解决的子目标，最后组装证明对象。

书写Lean的心流通常追问“怎样把目标化约成已知条件？”；Litex 常问“由已知条件能建立什么事实？”差异在默认方向，不在逻辑标准。

<a id="two-directions"></a>

<details>
<summary><strong>小例子：同一条代数等式的自上而下与自下而上写法</strong></summary>

这个例子展示同一等式的两种推进方向。Lean 从目标出发，每条 `rw` 指定事实、匹配方向和替换：

```lean
-- Using facts from the local context.
example (a b c d g f : ℝ) (h : a * b = c * d) (h' : g = f) :
    a * (b * g) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]
```

Litex 从 `a * (b * g)` 写出等式链，逐步到达 `c * (d * f)`。当前内核可验证这个由左向右的方向：

```litex
claim:
    ?forall a, b, c, d, g, f R:
        a * b = c * d
        g = f
        =>:
            a * (b * g) = c * (d * f)
    a * (b * g) = (a * b) * g = (c * d) * g = (c * d) * f = c * (d * f)
```

四个等号依次使用乘法结合、`a * b = c * d`、`g = f` 和再次结合。Lean 指定下一步如何改写目标；Litex 写出沿途应当成立的事实，再由内核寻找相邻等式的依据。

</details>

<details>
<summary><strong>设计空间中的位置：前向证明并非 Litex 首创</strong></summary>

Mizar、Isar、ACL2 和 Naproche 已支持前向文本、定理累积或逐步检查，因此“自下而上”并非 Litex 独有。Litex 检验的是组合：普通事实自动触发局部验证，通过后扩展上下文，同时让已接受或停下来的路径保持可见，供用户或人工智能检查和修复；只有常规验证不足时才写显式证明结构。更完整的比较见第 4 节的小结“Litex 与 Naproche——相近目标，不同核心接口”。

</details>

<a id="execution-model"></a>

## 4. 每句话都留下什么：可检查知识记录

我们读数学时，一句话从来不是孤零零地出现。写下一个事实的同时，我们也会在脑中浮现它所依赖的定义、前提和前面已经确认的事实；这些内容共同形成一个不断生长的上下文，后面的推理便在这片已经建立的基础上继续向前。

Litex 想做的，是把这条通常只存在于脑中的数学心流，逐句化成代码：源码写下要建立的对象和要验证的事实，已经定义好的概念和已经证明的事实留在上下文中，后续语句在它们之上继续生长。

*Litex最与众不同的点是，它的运行过程不是黑箱。任何语句是如何成立的，引入了什么概念，对整个证明上下文产生了什么作用，都会被输出出来*。换句话说：你阅读的不只是源码本身；源码以外，每句话背后的数学依据也被摊开给你看——语言帮你证，你给出证什么。正是因为 Litex 有这样的结构化输出，从一开始的设计上，Litex 就被设计成能编译成 Lean（或对应到其他形式化语言），并将整个数学证明中概念和概念、事实和事实之间的关系严格地呈现出来；早期实验保留了部分数学场景的 Lean 产物，当前构建尚未接入编译入口。它记录并输出了每句话为什么成立、使用了哪些依据、产生了哪些引申，以及哪些内容真正进入了后续的数学上下文。

先看一个最小的连续片段：

```litex
let a = 1
a + 1 = 2
```

第一句是定义（`define`）：它引入对象，并把定义事实 `a = 1` 存入上下文。第二句是验证（`verify`）：它读取当前上下文，检查 `a + 1 = 2` 的良定义性，沿着 `a = 1` 做透明定义化简，再使用数值规范化规则。通过后，第二条事实进入当前上下文，成为后续语句可以继续使用的基础。

下面是这片代码的执行结果。

<details>
<summary><strong>展开查看：Litex执行结果</strong></summary>

```json
{
  "kind": "run",
  "success": true,
  "target": "eval",
  "path": null,
  "detail": "normal",
  "session_error": null,
  "statement_results": [
    {
      "success": true,
      "statement": "let a = 1",
      "proof_method": { "type": "define_obj" },
      "stores": ["a = 1"],
      "infers": []
    },
    {
      "success": true,
      "statement": "a + 1 = 2",
      "proof_method": {
        "type": "builtin_rule",
        "rule_name": "Calculation",
        "message": "Both sides evaluate to the same number"
      },
      "stores": ["a + 1 = 2"],
      "infers": []
    }
  ]
}
```

</details>

这份记录把“这句话为什么能写下来”拆成了可追踪的局部步骤：先确认 `a + 1` 的参数满足运算所需的集合条件；再沿着已定义的 `a = 1` 透明化简为 `1 + 1 = 2`；最后由数值规范化规则完成计算。对读者来说，它至少回答了五个局部问题：

| 读者想知道什么 | 在记录里看哪里 |
| --- | --- |
| 跑了哪一句 | `statement` |
| 是否成功 | 语句的 `success`，以及整次运行的 `success` / `session_error` |
| 为什么成立 | `proof_method`（规则名、引用、定义路径等） |
| 为什么停下 | `why_failed.phase` 与 `why_failed.goal` |
| 什么进入了后续上下文 | `stores` 与 `infers` |

Normal JSON 是面向人与工具的日常记录。完整的 verify/exec 证据树仍留给 Lean 回放与详细工具使用；它不是日常 `-e` / `-f` / `-r` 打印的内容。

例如，`let a = 1` 是定义符号 `a`，并记录 `a = 1`；`a + 1 = 2` 则是在当前上下文中验证一个事实。良定义性检查先确认语句是否有意义：例如 `1 / 0 = 1 / 0` 虽然两边形式相同，但 `0` 不能作为除法允许的分母，因此这个语句不满足良定义性要求。

<details>
<summary><strong>展开查看：Litex执行结果</strong></summary>

当我们输入 `1 = 0` 时，Litex 的 Normal JSON 输出是

```json
{
  "kind": "run",
  "success": false,
  "target": "eval",
  "path": null,
  "detail": "normal",
  "session_error": null,
  "statement_results": [
    {
      "success": false,
      "statement": "1 = 0",
      "why_failed": {
        "phase": "search_proof",
        "goal": "1 = 0"
      },
      "stores": [],
      "infers": []
    }
  ]
}
```

这样的错误输出也是很宝贵的。当我们设计人类-AI-Litex交互流时，我们可以记录下来我们曾经犯过的错误，就能积累更多的数学形式化经验，让代码书写越来越高效和正确。

</details>

*Litex的核心就是这个简明、严谨、格式化的验证流输出——它把“这句话为什么对”从脑内默会变成可读记录。*从一条用户可以读懂并参与的执行路径出发，Litex 同时保留一份结构化知识记录。这份记录起到了4个作用：

1. **给人阅读**：把语句、依据和上下文变化做成交互式教科书。你读的是源码；你同时得到的是源码背后的数学原理。初学者不必再因为不知道某句话为什么成立而停在原地。
2. **给人工智能协作**：把每次成功、停止和失败的依据返回给人工智能，使它可以写 Litex、根据反馈自动纠错并逐步改进，形成“人—人工智能—Litex”的循环。
3. **给知识结构使用**：从定义、事实、引用和引申中生成定义与定理的依赖关系图，直观展示每个概念如何相互连接。
4. **给 Lean 复核（目标）**：根据记录中的定义、事实和验证依据，生成保持原命题含义的 Lean 证明，再交给 Lean 内核检查。当前构建没有这条编译入口。

![Litex 事实关系图示例](https://litexlang.com/_next/image?url=%2Fassets%2Fknowledge_graph.png&w=640&q=75)


我相信，这个输出流的功能肯定不止上述这些。我们希望更多的场景在未来的AI时代能被挖掘到。

<details>
<summary><strong>小结：Litex 的设计体现了它的哪些数学观</strong></summary>

Litex 把数学实践看成两种动作的往返：

1. **定义**（`define`）建立对象、关系、函数和可复用接口，给领域建立词汇。
2. **验证**（`verify`）在当前上下文中确认哪些事实成立，并保存它们的依据。
3. 每条已接受语句都会改变后续证明的可用前提；前文不是背景装饰，而是后文的基石。
4. 验证结果同时保留“为什么成立”和适用范围内的推断，而不只给出一个真假标签。
5. 常见数学对应优先由少量可组合的对象、关系、逻辑结构、内置规则和标准库提供；目标是覆盖广泛的集合论数学，而不是为每个表述增加一个互相重叠的特殊接口。当前覆盖仍在持续扩展和审计。

这五点中的任何一点，单独拿出来都不是 Litex 独有；其他语言也可能在某一个方向做得很好。Litex 的设计重点在于把它们组合成一条连续的数学工作流：定义建立词汇，验证在当前上下文中确认事实，记录保存依据和引申，后续语句在前文基础上继续生长，同一份记录再同时服务于人、人工智能、依赖关系图和 Lean。正是这个组合，让形式化过程更贴近日常数学思考，也更适合人工智能参与，更符合人工智能时代的数学追求，并以人的理解和判断为出发点。这是 Litex 正在检验的设计假设，而不是对其他语言能力的排他性断言。

最最重要的是：Litex 是一个真的能帮助人理解数学的工具。它不只告诉你答案，还把答案为什么成立、依赖什么、会为后文留下什么都摊开在眼前；在人工智能时代，当答案可以被大量生成时，这种帮助人保持理解的能力尤其珍贵。

</details>

<details>
<summary><strong>实现摘要：记录如何生成</strong></summary>

实现可以随着规则、标准库、知识图和 Lean 接口不断扩大，而不必改变读者对核心流程的理解：

```text
Litex 源码
  → 解析为带类型的对象和语句
  → 执行定义或验证
  → 检查良定义性、形状、依据和前提
  → 生成结构化执行结果
  → 提交候选或回滚候选
  → 更新已接受上下文，并在适用时运行推断
  → 让用户和人工智能看见已接受路径、上下文变化和修复边界
  → 为工具和交互式视图保留可检查知识记录
  → 在需要时提供 JSON 和关系图等机器可读或结构化视图
  → 后续集成目标：把支持范围内的证据交给 Lean 编译器和内核
```

可检查知识记录是这条可见执行路径的结构化形式，不是从终端文字事后拼出的日志。JSON 是在工具需要时使用的一种机器可读表示；用户不必阅读 JSON，也能跟随并修复执行过程。关系图是联系的一种可选视图，Lean 则是受支持路径的独立复核端。实现规模可以增长，但这些职责不需要随规则数量一起膨胀。

</details>

<a id="interaction-loop"></a>

## 5. 人类-AI-Litex 循环工作流构建

前文说明了一条定义或事实被执行后，Litex 会留下什么。更大的数学发展还需要另一层：人类和人工智能如何利用这些记录继续构造，同时把数学意图、候选方案、验证决定和维护中的源码分开。

Litex 从集合论对象和成员关系出发，让事实导向的源码自下而上地生长一个已验证的上下文，并直接输出结构化验证结果，而不是只返回一个最终真假标签。正是这种设计组合，构成了 Litex 的独特性，让构建`人类-AI-Litex循环`的方法非常分工明确：

```text
人类提出数学问题及其解答意图
                         ↓
AI 把问题与解答拆成有序片段
                         ↓
              ┌──── 片段形式化循环 ────┐
              │                         │
              ▼                         │
AI 把当前片段写成 Litex 代码             │
                         ↓              │
Litex 结构化验证结果                    │
   ├─ success                           │
   │     → 记录这段代码                 │
   │     → 记录 Litex 如何运行它        │
   │     → 进入下一片段 ────────────────┘
   └─ RolledBack
         → 基于证据的诊断
         → 修复同一个片段，再试
                         ↓
全部成功片段按顺序衔接 → 问题得到解决与形式化
                         ↓
人类专家做基本校验
                         ↓
这些 Litex 代码成为后续其他问题的基石
```

> 任何单独的Litex的特性，都能在历史上的某一个形式化语言上找到影子：可读性上，Naproche有非常接近课本的书写格式；基于集合论？Mizar就是；建立了丰富生态的其他形式化语言更是很多。Litex集众语言之长，形成了自己的设计风格，使之能面向广大的非形式化专业用户群体，适应AI时代的需求。

> 在数学之外，其他对可信推理有强需求的行业，如AI安全、软件验证，都对这样的人类-AI-Litex循环产生了兴趣。

片段形式化循环中，执行流按源代码顺序推进，每一轮只处理一个定义、定理或小型证明片段。AI 提出该片段的 Litex 代码；Litex 返回结构化验证结果，决定这一轮能否继续。若成功，结果会同时留下两样东西：这段已被接受的源码，以及这段代码如何被检查、依据什么成立的运行记录——没有后者，AI 就不知道下一步该信任什么、该修复什么；有了后者，成功片段才能成为后续片段的已接受前提，失败片段也能被精准诊断而不污染上下文。当全部片段成功衔接后，问题既被解决，也被形式化；人类专家再做基本校验。通过校验的 Litex 代码与其运行记录，才会作为可复用的数学基石，支撑后续其他问题。换言之，推动循环前进的，不是 AI 的流畅表述，而是 Litex 每一次可检查、可回放、可交接的输出。

因此，Litex 留下的不只是最终可复用的 `.lit` 源码。它还把 AI 在形式化过程中的尝试本身保存下来：哪里对了、哪里错了，怎么对的、怎么错的。这些源码以外的经验同样本质——没有它们，后人只能看见一份已经写好的证明；有了它们，人和 AI 才能回看构造路径、复用修复方式，并把一次求解变成可学习的形式化经验。

**成功时读者应看到什么。** 当这条人类–AI–Litex 循环真正跑通时，读者不必先成为证明助手专家，也能直接看到：一类教材式定义与定理可以按数学意图读写并被机器检查；局部失败会停在当前片段、给出可据以修复的依据，且不污染已接受上下文；成功片段按顺序衔接后，留下可复用的 `.lit` 源码与可回放的运行记录，供后续问题继续引用。机器通过仍须人类做基本校验——这是循环的终点判据，不是旁支装饰。

<details>
<summary><strong>示例：按流程图走一遍片段形式化循环</strong></summary>

下面是一个独立的小例子，步骤与上文流程图一一对应。它故意不完整，只用来看清循环本身：先定义语言，再验证定义之下能推出什么。

<a id="convergence-example"></a>

**1. 人类提出数学问题及其解答意图**

> 先定义数列收敛：对任意正误差 `ε`，存在位置 `N`，使此后每项都足够接近极限。再证明：若 `{s(n)}` 收敛到 `a`，则 `{c * s(n)}` 收敛到 `c * a`。

**2. AI 把问题与解答拆成有序片段**

针对这个问题，AI 可以先拆成例如：

1. 定义“最终足够接近”，这是一个谓词，用`prop`定义
2. 定义“收敛”，这是一个谓词，用`prop`定义
3. 写出并证明 `thm`：数乘保持收敛  

**3. 片段形式化循环：前两个片段成功——先把定义写进上下文**

AI 先提交两个定义；Litex 返回成功。于是留下这段源码，以及 Litex 如何运行它的记录。已接受上下文增长，后面的定理片段可以按定义展开。

```litex
# “最终足够接近”：从 N0 起，每项都落在误差 epsilon 内。
prop is_eventually_close(s fn(n N) R, a R, epsilon R+, N0 N):
    forall n N:
        n >= N0
        =>:
            abs(s(n) - a) < epsilon

# “收敛到 a”：任意正误差都存在这样一个 N0。
prop converges_to(s fn(n N) R, a R):
    forall epsilon R+:
        exist N0 N st {$is_eventually_close(s, a, epsilon, N0)}
```

**4. 同一循环中的失败与修复：证明数乘保持收敛**

AI 先试图在没有构造 `forall / exist` 结构的情况下，直接 `by def` 得到新数列的收敛。Litex 返回失败并回滚：

```json
{
  "kind": "run",
  "success": false,
  "detail": "normal",
  "session_error": null,
  "statement_results": [
    {
      "success": false,
      "statement": "...",
      "why_failed": {
        "phase": "search_proof",
        "goal": "$converges_to(fn(n N) R {c * s(n)}, c * a)"
      },
      "stores": [],
      "infers": []
    }
  ]
}
```

已接受上下文不变。记录说明：定义给出的是要证明的形状，不是现成结论；必须先为每个 `epsilon` 取出并交出合适的 `N0`。AI 只修这一片段：

> **迁移示例：** 当前 `src/` 检查停在 `def_thm` (`thm`)；以下保留写法不算已验证结果。

<!-- litex:skip-test -->
```litex
thm converges_to_mul_const:
    ? forall s fn(n N) R, a, c R:
        $converges_to(s, a)
        =>:
            $converges_to(fn(n N) R {c * s(n)}, c * a)
    claim:
        ? forall epsilon R+:
            exist N0 N st {$is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, N0)}
        abs(c) + 1 > 0
        epsilon / (abs(c) + 1) $in R+
        obtain N0 from exist K N st {$is_eventually_close(s, a, epsilon / (abs(c) + 1), K)}
        witness exist K N st {$is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, K)} from N0:
            forall n N:
                n >= N0
                =>:
                    abs(s(n) - a) < epsilon / (abs(c) + 1)
                    abs(c * s(n) - c * a) = abs(c) * abs(s(n) - a)
                    abs(c) * abs(s(n) - a) <= (abs(c) + 1) * abs(s(n) - a) < epsilon
                    abs(fn(k N) R {c * s(k)}(n) - c * a) < epsilon
            by def $is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, N0)
    by def $converges_to(fn(n N) R {c * s(n)}, c * a)
```

Litex 再次检查后成功。于是同样留下源码与运行记录。

**5. 全部成功片段衔接 → 问题得到解决与形式化**

各成功片段按顺序连成一份连续的 Litex 发展：先有定义语言，再有定义之下的定理。最终源码只有成功前缀；失败尝试仍被记录，解释修复，却不成为数学前提。

**6. 人类专家做基本校验**

专家核对：意图是否仍是“定义收敛并证明数乘保持”、`prop` 是否忠实于分析定义、估计是否可信。机器通过不等于免审。

**7. 这些 Litex 代码成为后续问题的基石**

通过校验后，这套收敛接口与数乘定理可被极限代数、连续函数等后续问题继续引用。留下的不只是当次证明，还有可复用的形式化地基，以及“哪里对了、哪里错了”的经验。

</details>

<a id="compatibility"></a>

## 6. Litex代码如何编译成Lean代码，并与Mathlib兼容（Experimental）

Litex 可独立工作，拥有语法、运行时和验证内核。如果你相信Litex内核是没有bug的，那它不编译成 Lean 也能为你检查良定义性与事实并提供反馈。

但在大型数学系统上，Lean有不可比拟的优势：Lean/Mathlib生态成熟、可复用的数学对象和定理库丰富、内核小而可审计。Litex希望能接入Lean的生态，如此Lean社区也能从Litex中受益，Litex可以在一些数学方向为Lean提供更易读、更易写的数学接口。

对支持的证明，独立的 Lean 检查有望减少对 Litex 验证器实现的依赖；前提是翻译保持原命题含义，生成的证明没有证明空洞，并且确实通过 Lean 内核。这是验证目标，不是当前构建已经提供的保证。

> **当前构建：** `Cargo.toml` 注册的是 `litex` 二进制，`src/lib.rs` 没有编译器模块。保留的 `lean/stmt_result_to_lean_compiler.sh` 指向当前缺失的 Cargo 二进制目标。下面是早期实验记录，未使用当前 `src/` 重新生成或通过 Lean 检查。

<details>
<summary><strong>示例：Litex代码如何编译成Lean</strong></summary>

Litex编译成Lean，并接入Mathlib-Style的Lean代码，要经过以下过程：

`Litex 源码 → Litex 验证 → ToLean 编译 → Lean 内核复核 → 手写 adapter → Mathlib 定理`

> Litex编译成Lean的过程非常像C语言代码编译成汇编。我们知道汇编语言的代码之所以看起来像乱码是因为源码里写了很多内存地址。不管是新开地址和使用该地址时都要显式把地址写出来。Lean代码给每个事实都取了名字，在调用对应事实时也需要显式地把名字附上。Litex的内核在处理Litex代码时，替用户维护了这样一张事实表，同时在验证时会按原子事实的谓词名为 key，从该事实表中搜索对应事实来辅佐证明当前想要证明的东西（为何能这样做、为何 Lean 很难直接照搬，见第 2 节）。这个搜索过程的分叉多（Litex有几百条内置验证规则）而不深（每个验证规则都很直白，任何内置规则可以被编译成若干条Lean的tactic）。

举例：我们想要证明前`n`个正奇数之和是`n^2`。我们先写下Litex的源码：

> **迁移示例：** 当前 `src/` 检查停在 `internal_bug: name n is already bound in an enclosing parse scope`；以下保留写法不算已验证结果。

<!-- litex:skip-test -->
```litex
have fn kth_odd(k Z) Z = 2 * k - 1

forall n Z:
    n >= 1
    =>:
        sum(1, n, kth_odd) $in Z

forall n Z:
    n^2 $in Z

thm sum_first_odds: 
    ? forall n Z:
        n >= 1
        =>:
            sum(1, n, kth_odd) = n^2
    by induc n from 1:
        ? sum(1, n, kth_odd) = n^2

        ? from n = 1:
            kth_odd(1) = 2 * 1 - 1 = 1
            sum(1, 1, kth_odd) = kth_odd(1) = 2 * 1 - 1 = 1 = 1^2

        ? induc:
            kth_odd(n + 1) = 2 * (n + 1) - 1
            sum(1, n + 1, kth_odd) = sum(1, n, kth_odd) + kth_odd(n + 1) = n^2 + kth_odd(n + 1) = n^2 + (2 * (n + 1) - 1) = (n + 1)^2
```

编译到Lean（不同的Litex版本编译出来的东西可能会不同）

```lean
-- Generated by StmtResultToLeanCompiler from main.lit. DO NOT EDIT.
import Litex

set_option linter.style.nameCheck false

namespace __Compiler_main

noncomputable def kth_odd : Litex.Fn Litex.Z Litex.Z :=
  { call := fun {__alpha} (__arg : __alpha) __arg_in => (((2 : ℤ) * Litex.In.rep __arg __arg_in) - (1 : ℤ)), callOwn := fun (__arg : ℤ) => (((2 : ℤ) * __arg) - (1 : ℤ)) }

theorem __fact0 : Litex.In kth_odd (Litex.fnSet Litex.Z Litex.Z) := by
  exact Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd

theorem __fact1 : Litex.Same kth_odd ({ call := fun {__alpha} (__arg : __alpha) __arg_in => (((2 : ℤ) * Litex.In.rep __arg __arg_in) - (1 : ℤ)), callOwn := fun (__arg : ℤ) => (((2 : ℤ) * __arg) - (1 : ℤ)) } : Litex.Fn Litex.Z Litex.Z) := by
  unfold kth_odd
  exact Litex.Same.refl ({ call := fun {__alpha} (__arg : __alpha) __arg_in => (((2 : ℤ) * Litex.In.rep __arg __arg_in) - (1 : ℤ)), callOwn := fun (__arg : ℤ) => (((2 : ℤ) * __arg) - (1 : ℤ)) } : Litex.Fn Litex.Z Litex.Z)

theorem __fact2 :
    ∀ (__p1 : ℤ) (__domain1 : Litex.Le (1 : ℂ) (((__p1) : ℂ))), Litex.In (Litex.sum (1 : ℤ) __p1 kth_odd) Litex.Z := by
  intro n __domain_f17
  have __infer2_0 : Litex.Lt (0 : ℂ) (((n) : ℂ)) := Litex.Lt.transLe (Litex.OrderBridge.ltOfComplexReals (show (0 : ℝ) < (1 : ℝ) by norm_num)) (__domain_f17)
  have __prior2_0 : Litex.In (Litex.sum (1 : ℤ) n kth_odd) Litex.Z := Litex.In.own Litex.Z ((Litex.sum (1 : ℤ) n kth_odd))
  exact __prior2_0

theorem __fact3 :
    ∀ (__p1 : ℤ), Litex.In (((((__p1) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) Litex.Z := by
  intro n
  have __prior3_0 : Litex.In (((((n) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) Litex.Z := Litex.Rules.complexIntPowNatInZ (n) (2 : ℕ)
  exact __prior3_0

theorem sum_first_odds :
    ∀ (n : ℤ) (__domain_f48 : Litex.Le (1 : ℂ) (((n) : ℂ))),
      Litex.Same (Litex.sum (1 : ℤ) n kth_odd) (((((n) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) := by
  intro n __domain_f48
  have __step4_29 : ∀ (__p1 : ℤ) (__domain1 : Litex.Le (1 : ℂ) (((__p1) : ℂ))), Litex.Same (Litex.sum (1 : ℤ) __p1 kth_odd) (((((__p1) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) := by
    intro __target_value __domain1
    have __target_ge_start_real : (((1 : ℤ)) : ℝ) ≤ (__target_value : ℝ) := by
      simpa [Litex.Le, Litex.OrderValue] using __domain1
    have __target_ge_start : (1 : ℤ) ≤ __target_value := by
      exact_mod_cast __target_ge_start_real
    exact Litex.Rules.integerInductionFrom (motive := fun __induction_value : ℤ => Litex.Same (Litex.sum (1 : ℤ) __induction_value kth_odd) (((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ)) (by
    have __step4_2 : (Litex.Same (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (1 : ℤ)) (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ))) ∧ (Litex.Same (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ)) (1 : ℂ)) := by
      exact ⟨Litex.Same.trans ((by
      unfold Litex.fnApplyCarrier kth_odd
      exact Litex.Same.intSubComplex (Litex.Same.intMulComplex (Litex.Same.intComplexOfEq (z := (2 : ℤ)) (by norm_num)) (Litex.Same.intComplexOfEq (z := ((1 : ℤ))) (by norm_cast))) (Litex.Same.intComplexOfEq (z := (1 : ℤ)) (by norm_num)))) (Litex.Same.refl (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ))), Litex.Same.ofEq (by norm_num [Litex.abs, Litex.min, Litex.max, Litex.tupleDim, Litex.TupleShape.dimension])⟩
    have __infer4_3 : Litex.Same (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (1 : ℤ)) (1 : ℂ) := Litex.Same.trans ((__step4_2).1) ((__step4_2).2)
    have __step4_4 : (Litex.Same (Litex.sum (1 : ℤ) (1 : ℤ) kth_odd) (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (1 : ℤ))) ∧ (Litex.Same (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (1 : ℤ)) (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ))) ∧ (Litex.Same (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ)) (1 : ℂ)) ∧ (Litex.Same (1 : ℂ) (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ)) := by
      exact ⟨Litex.Same.trans (Litex.Same.symm (Litex.Same.symm (Litex.Same.trans (Litex.Rules.integerRangeSumSingleOwn (1 : ℤ) kth_odd) ((__step4_2).1)))) (Litex.Same.symm ((by
      unfold Litex.fnApplyCarrier kth_odd
      exact Litex.Same.intSubComplex (Litex.Same.intMulComplex (Litex.Same.intComplexOfEq (z := (2 : ℤ)) (by norm_num)) (Litex.Same.intComplexOfEq (z := ((1 : ℤ))) (by norm_cast))) (Litex.Same.intComplexOfEq (z := (1 : ℤ)) (by norm_num))))), ⟨(__step4_2).1, ⟨(__step4_2).2, Litex.Same.ofEq (by norm_num [Litex.abs, Litex.min, Litex.max, Litex.tupleDim, Litex.TupleShape.dimension])⟩⟩⟩
    have __infer4_5 : Litex.Same (Litex.sum (1 : ℤ) (1 : ℤ) kth_odd) (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ)) := Litex.Same.trans ((__step4_4).1) ((__step4_4).2.1)
    have __infer4_6 : Litex.Same (Litex.sum (1 : ℤ) (1 : ℤ) kth_odd) (1 : ℂ) := Litex.Same.trans (Litex.Same.trans ((__step4_4).1) ((__step4_4).2.1)) ((__step4_4).2.2.1)
    have __infer4_7 : Litex.Same (Litex.sum (1 : ℤ) (1 : ℤ) kth_odd) (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ) := Litex.Same.trans (Litex.Same.trans (Litex.Same.trans ((__step4_4).1) ((__step4_4).2.1)) ((__step4_4).2.2.1)) ((__step4_4).2.2.2)
    have __infer4_8 : Litex.Same (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (1 : ℤ)) (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ) := Litex.Same.trans (Litex.Same.trans ((__step4_4).2.1) ((__step4_4).2.2.1)) ((__step4_4).2.2.2)
    have __infer4_9 : Litex.Same (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ)) (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ) := Litex.Same.trans ((__step4_4).2.2.1) ((__step4_4).2.2.2)
    have __infer4_10 : Litex.In (1 : ℂ) Litex.RPos := (Litex.In.congr ((__step4_4).2.2.2) Litex.RPos).mpr (Litex.Rules.complexEqRealInRPos (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ) (1 : ℝ) (by norm_num) (by norm_num))
    have __infer4_11 : Litex.Positive (1 : ℂ) := (by simpa [Litex.In.rep] using (Litex.Rules.positiveOfInRPos (__infer4_10)))
    have __infer4_12 : Litex.In (Litex.sum (1 : ℤ) (1 : ℤ) kth_odd) Litex.RPos := (Litex.In.congr (__infer4_7) Litex.RPos).mpr (Litex.Rules.complexEqRealInRPos (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ) (1 : ℝ) (by norm_num) (by norm_num))
    have __infer4_13 : Litex.Positive (Litex.sum (1 : ℤ) (1 : ℤ) kth_odd) := (by simpa [Litex.In.rep] using (Litex.Rules.positiveOfInRPos (__infer4_12)))
    have __infer4_14 : Litex.In (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (1 : ℤ)) Litex.RPos := (Litex.In.congr (__infer4_8) Litex.RPos).mpr (Litex.Rules.complexEqRealInRPos (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ) (1 : ℝ) (by norm_num) (by norm_num))
    have __infer4_15 : Litex.Positive (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (1 : ℤ)) := (by simpa [Litex.In.rep] using (Litex.Rules.positiveOfInRPos (__infer4_14)))
    have __infer4_16 : Litex.In (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ)) Litex.RPos := (Litex.In.congr (__infer4_9) Litex.RPos).mpr (Litex.Rules.complexEqRealInRPos (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ) (1 : ℝ) (by norm_num) (by norm_num))
    have __infer4_17 : Litex.Positive (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ)) := (by simpa [Litex.In.rep] using (Litex.Rules.positiveOfInRPos (__infer4_16)))
    exact (by simpa using (__infer4_7))) (fun (__induction_value : ℤ) (__induction_ge_start : (1 : ℤ) ≤ __induction_value) (__induction_hypotheses : Litex.Same (Litex.sum (1 : ℤ) __induction_value kth_odd) (((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ)) => by
    have __infer4_18 : Litex.Lt (0 : ℂ) (((__induction_value) : ℂ)) := Litex.Lt.transLe (Litex.OrderBridge.ltOfComplexReals (show (0 : ℝ) < (1 : ℝ) by norm_num)) ((by
      have __induction_ge_start_real : (((1 : ℤ)) : ℝ) ≤ (__induction_value : ℝ) := by
        exact_mod_cast __induction_ge_start
      simpa [Litex.Le, Litex.OrderValue] using __induction_ge_start_real))
    have __infer4_19 : Litex.In (Litex.sum (1 : ℤ) __induction_value kth_odd) Litex.RPos := (Litex.In.congr (__induction_hypotheses) Litex.RPos).mpr (Litex.Rules.positiveIntegerRationalPowInRPos (__induction_value) (2 : ℤ) (__infer4_18) (by norm_num))
    have __infer4_20 : Litex.Positive (Litex.sum (1 : ℤ) __induction_value kth_odd) := (by simpa [Litex.In.rep] using (Litex.Rules.positiveOfInRPos (__infer4_19)))
    have __step4_21 : Litex.Same (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ))) (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ)) := by
      exact Litex.Same.trans ((by
      unfold Litex.fnApplyCarrier kth_odd
      exact Litex.Same.intSubComplex (Litex.Same.intMulComplex (Litex.Same.intComplexOfEq (z := (2 : ℤ)) (by norm_num)) (Litex.Same.intComplexOfEq (z := ((__induction_value + (1 : ℤ)))) (by norm_cast))) (Litex.Same.intComplexOfEq (z := (1 : ℤ)) (by norm_num)))) (Litex.Same.refl (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ)))
    have __step4_22 : (Litex.Same (Litex.sum (1 : ℤ) (__induction_value + (1 : ℤ)) kth_odd) ((((Litex.sum (1 : ℤ) __induction_value kth_odd) : ℤ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ))))) ∧ (Litex.Same ((((Litex.sum (1 : ℤ) __induction_value kth_odd) : ℤ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ)))) ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ))))) ∧ (Litex.Same ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ)))) ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ)))) ∧ (Litex.Same ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ))) ((((((__induction_value) : ℚ)) + (1 : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ)) := by
      exact ⟨Litex.Rules.integerRangeSumSplitLastOwn (1 : ℤ) __induction_value kth_odd ((by simpa [Litex.Le, Litex.OrderValue] using ((by
      have __induction_ge_start_real : (((1 : ℤ)) : ℝ) ≤ (__induction_value : ℝ) := by
        exact_mod_cast __induction_ge_start
      simpa [Litex.Le, Litex.OrderValue] using __induction_ge_start_real)))), ⟨Litex.Same.intCastAddComplex (__induction_hypotheses) (Litex.Same.intComplex ((Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ))))), ⟨Litex.Same.addCongrRightInt (Litex.Same.refl ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ))) (__step4_21), Litex.Same.trans (Litex.Same.refl (((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ))))) (Litex.Same.trans (Litex.Same.ofEq ((show ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ))) = ((((((__induction_value) : ℚ)) + (1 : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) from (by norm_cast <;> ring_nf)))) (Litex.Same.symm (Litex.Same.refl (((((((__induction_value) : ℚ)) + (1 : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ)))))⟩⟩⟩
    have __infer4_23 : Litex.Same (Litex.sum (1 : ℤ) (__induction_value + (1 : ℤ)) kth_odd) ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ)))) := Litex.Same.trans ((__step4_22).1) ((__step4_22).2.1)
    have __infer4_24 : Litex.Same (Litex.sum (1 : ℤ) (__induction_value + (1 : ℤ)) kth_odd) ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ))) := Litex.Same.trans (Litex.Same.trans ((__step4_22).1) ((__step4_22).2.1)) ((__step4_22).2.2.1)
    have __infer4_25 : Litex.Same (Litex.sum (1 : ℤ) (__induction_value + (1 : ℤ)) kth_odd) ((((((__induction_value) : ℚ)) + (1 : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) := Litex.Same.trans (Litex.Same.trans (Litex.Same.trans ((__step4_22).1) ((__step4_22).2.1)) ((__step4_22).2.2.1)) ((__step4_22).2.2.2)
    have __infer4_26 : Litex.Same ((((Litex.sum (1 : ℤ) __induction_value kth_odd) : ℤ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ)))) ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ))) := Litex.Same.trans ((__step4_22).2.1) ((__step4_22).2.2.1)
    have __infer4_27 : Litex.Same ((((Litex.sum (1 : ℤ) __induction_value kth_odd) : ℤ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ)))) ((((((__induction_value) : ℚ)) + (1 : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) := Litex.Same.trans (Litex.Same.trans ((__step4_22).2.1) ((__step4_22).2.2.1)) ((__step4_22).2.2.2)
    have __infer4_28 : Litex.Same ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ)))) ((((((__induction_value) : ℚ)) + (1 : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) := Litex.Same.trans ((__step4_22).2.2.1) ((__step4_22).2.2.2)
    exact (by simpa using (__infer4_25))) __target_value __target_ge_start
  have __c4_0 : Litex.Same (Litex.sum (1 : ℤ) n kth_odd) (((((n) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) := (by
    simpa [Litex.In.rep, Litex.fnApply, Litex.fnApplyOwn, Litex.abs, Complex.ext_iff, Real.norm_eq_abs] using (__step4_29 n (by
    simpa [Litex.In.rep, Litex.fnApply, Litex.fnApplyOwn, Litex.abs, Complex.ext_iff, Real.norm_eq_abs] using (__domain_f48))))
  exact __c4_0

end __Compiler_main

```

生成的代码是Lean代码，但是是在Litex的语义下的Lean代码。我们稍加一个adapter，将 Litex 的表示桥接到 Mathlib：

```lean
import Generated

/-! The handwritten interface from generated Litex evidence to native Mathlib. -/

namespace Adapter

/-- Export the generated theorem as ordinary Mathlib equality. -/
theorem sumFirstOddsNative
    (n : ℤ)
    (oneLeN : (1 : ℤ) ≤ n) :
    ∑ k ∈ Finset.Icc (1 : ℤ) n, (2 * k - 1) = n ^ 2 := by
  have generated :=
    __Compiler_main.sum_first_odds n
      (Litex.OrderBridge.leOfComplexReals (by exact_mod_cast oneLeN))
  have exactComplexEq :
      ((Litex.sum (1 : ℤ) n __Compiler_main.kth_odd : ℤ) : ℂ) =
        ((n ^ 2 : ℤ) : ℂ) := by
    calc
      ((Litex.sum (1 : ℤ) n __Compiler_main.kth_odd : ℤ) : ℂ) =
          ((((n : ℚ) ^ (2 : ℤ) : ℚ) : ℂ)) :=
        Litex.Same.intComplexEq generated
      _ = ((n ^ 2 : ℤ) : ℂ) := by norm_cast
  exact_mod_cast exactComplexEq

end Adapter

```

桥接完成后，结论可以使用 Mathlib 的原生接口：

```lean
import Adapter

/-- A native theorem whose statement is entirely independent of Litex. -/
theorem firstHundredPositiveOddIntegersSum :
    ∑ k ∈ Finset.Icc (1 : ℤ) 100, (2 * k - 1) = 10000 := by
  exact Adapter.sumFirstOddsNative 100 (by norm_num)

```

这条实验路线希望让 Litex 成为更易读的 Lean 前端：用户先从 Litex 源码理解证明，再把支持的证据交给 Lean 检查并接入 Mathlib。从一开始的设计上，Litex 就被设计成能编译成 Lean；早期实验保留了部分数学场景的 Lean 产物，当前构建尚未接入编译入口。我相信这是非常值得探索的一个方向。

</details>

<a id="summary-bottom-up-and-top-down"></a>

<details>
<summary><strong>个人思考：Litex补齐了AI推理的范式缺口？</strong></summary>

在数学实践中，自下而上的证明流（从前提出发，积累更多事实），与自上而下的证明流（分解最终结论，直到最终和前提匹配上），构成了数学证明时的不同视角和思路。Litex的源码代表了前者的思维模式，Lean代码代表了后者。那么AI更偏好哪一种思维模式呢？

先看自下而上的证明流。大部分数学教材都是基于自下而上的行文模式写的，这也是人类更适应的思维范式（试想，我们不会从数学最后一页开始读书！）。大模型都是在互联网中的数学知识上进行训练的，因此AI更容易阅读Litex代码。同时，让AI Agent去写Litex代码时，让它和Litex的输出交互，了解每段证明为什么对，哪里出错，更容易形成`人类-AI-Litex`的证明流构建。

再看自上而下的证明流。大模型的训练围绕着目标函数和奖励信号展开。因而，AI 未必天然具备稳定的、从第一性原理自下而上展开的推理能力；在许多任务中，它更容易从期望结果或评价信号反向组织一条看起来能够到达结果的路径。

因此，两种思维模式都很宝贵：自下而上适合积累可复用的局部事实、暴露中间依据；自上而下适合澄清目标、选择方向、压缩搜索空间。Litex 与 Lean 的连接，正可以把这两种方向放进同一条可检查的证据链，并让人类和 AI 在各自擅长的方向上协作。

</details>

<a id="executable-code"></a>

## 7. 把证明编译成可执行代码（Python / C）（Experimental）

Litex 还在做另一条实验性编译路线：把（部分）已验证的证明直接变成可运行代码——目前主要是受支持的数值定义与 `algo` 片段，抽出为 Python 或 C。重点不是「导出整座定理库」，而是：计算步骤在 Litex 里检查过之后，同一份写法可以变成你能跑的可执行代码。

这条路线刻意做窄，且标明实验性。它不是整门 Litex 到 Python/C 的编译器；覆盖限于可抽取定义。命令行见 CLI 文档中的 `-extractpython` / `-extractc`。

<details>
<summary><strong>示意：牛顿法逼近 √2 的单步 → Python / C</strong></summary>

同一份用于科学计算的 Litex 证明，可以转化成可执行代码。例如牛顿法逼近 √2 的单步更新：

> **迁移示例：** 当前 `src/` 检查停在 `parse_error: undefined name newton_sqrt_two_step`；以下保留写法不算已验证结果。

<!-- litex:skip-test -->
```litex
have fn newton_sqrt_two(x R+) R+ = (x + 2 / x) / 2

claim:
    ? forall x R+:
        newton_sqrt_two_step(x) = newton_sqrt_two(x)
    newton_sqrt_two_step(x) = (x + 2 / x) / 2 = newton_sqrt_two(x)

algo newton_sqrt_two_step(x R) R by cases:
    case x = 0: 1
    case x != 0: (x + 2 / x) / 2
```

转化为 Python：

```python
def newton_sqrt_two_step(x):
    if x == 0.0:
        return 1.0
    elif x != 0.0:
        return ((x + (2.0 / x)) / 2.0)
    raise AssertionError("unreachable verified Litex cases")
```

转化为 C：

```c
#include <stdlib.h>

double newton_sqrt_two_step(double x) {
    if (x == 0.0) {
        return 1.0;
    }
    else if (x != 0.0) {
        return ((x + (2.0 / x)) / 2.0);
    }
    abort();
}
```

</details>

<a id="ecosystem-role"></a>

## 8. 从语言到生态：Litex 想扮演什么角色

所有的设计合在一起，使 Litex 希望成为人和 AI 共同生产、使用可检查推理的基础设施。

**Litex 面向人类与 AI：既是可读推理前端，也是可信推理数据生产层，并尝试通过 Lean/Mathlib 接入现有生态。** 它希望也服务于 AI、工程师和其他领域实践者。

未来的数学家工作流，一定会是AI+人类协同工作，做出证明，然后把证明生成对应的形式化代码确保其正确性。这里生成的形式化代码可以是Lean，可以是Litex。Litex希望成为Lean的更可读的前端语言，降低形式化代码的阅读和书写门槛。

前面的几节说明了，这个角色并不是若干功能的简单相加。集合论对象、事实导向源码、自下而上生长的已验证上下文、极简语法、贴近自然数学的表达，以及结构化验证结果，共同进入了同一套协议，使数学本身和数学的构造证据都能够被保存。

| 生态角色 | Litex 希望产生的实际成果 |
| --- | --- |
| 可读推理的前端 | 人可以直接审核的数学对象、条件、中间事实和结论 |
| 可信推理数据的生产层 | 经过机器检查的事实与验证来源、明确的停止边界，以及被显式标出的可信边界 |
| 现有生态的接入层 | 从一开始的设计上即面向 Lean 编译与复核（第 6 节，Experimental）；早期 Lean 产物仅记录实验覆盖，当前 `src/` 未接入编译器；以及明确分离、由 AI 或人类编写的新增 Lean/Mathlib adapter |
| 证明 → 可执行代码（Experimental） | 把已检查的计算片段转化成可运行的 Python / C（第 7 节） |

当然，Litex现阶段更像是处于 `proof of an idea` 的阶段。即便它本身已经有几十万行代码，它在行业上下游中的探索仍然稀缺。这也是Litex下一阶段会着重关注的：如何让从0到1的原始创新，成为从1到10的早期价值兑现。对Litex感兴趣的朋友可以联系 litexlang@outlook.com 。

<details>
<summary><strong>Litex的生态位</strong></summary>

形式化语言的供需关系是必然存在的。语言设计通常由 1–2 人主导：一边设计，一边工程化、一边迭代；设计人数少，才能尽量保证设计一致性——这几乎是任何编程语言的常态。但要把一门形式化语言真正做出来，工程量极大：内核、规则、标准库、工具链、文档与生态，远不是同一两个人在传统人力条件下能同时扛住的。没有 AI 协助实现与迭代时，像 Litex 这样「设计面必须小、工程面却巨大」的项目几乎不可能落地；正是 AI 的发展，才使这类项目变得可尝试。

与此同时，新行业的出现也在抬高对形式化的需求。编程语言很少凭空流行。它们通常诞生于新的技术能力与新的社会需求交汇之处：Fortran 伴随大型机计算能力和高性能计算需求出现，C 与 Unix 的系统编程需求彼此塑造，JavaScript 与 Java 随互联网时代的前端和后端开发普及，Python 和 CUDA 则分别回应了 AI 框架快速迭代与底层高性能计算的需要。Lean 的新一轮发展，也与 AI for Math 对可靠形式化的需求高度重合。

Litex 想寻找的，正是下一个由 AI 时代催生、目前还难以准确命名的场景。AI 将持续生成大量候选推理，新的知识工作也会因此需要更低成本的检查、解释、组织和复用。形式化语言行业能否接住这波浪潮，也是需要共同考虑的问题。我相信这样的场景应该会很快出现。

</details>

<a id="conclusions"></a>

## 9. 追寻与众不同的艺术

<!-- 这一段比较理想主义一点。因为AI时代大家过度关注实用主义了，容易忽略一个原生的、创新的、与众不同的新解决方案带来的长期的影响力。不管是数学界，还是任何科学，大家都鼓励对同一问题的不同角度、不同解决方案的出现。这样的不同的观点，往往才是科学史上真正突破的来源，最终可能会带来更大的效益提高。 -->

在星光熠熠的科学史上，对同一问题的全新视角、全新解答，往往极大推导了原来领域的发展，甚至催生了全新的学科。在效率至上的AI时代，即使在数学这么以长期主义著称的学科，我们仍然很容易迷失在抢先发布、刷榜宣传的局部最优解中，而忽略了对第一性原理的重新思考和原始创新。

这并不意味着要否定已经取得巨大成功的 Lean。Lean 以优雅的类型论、可靠的内核和丰富的 Mathlib 生态，证明了数学能够被严谨地工程化。Litex 更想追问的是：在「从一开始的设计上就能编译成 Lean、接受内核复核；当前构建尚未接入编译入口」这一前提下，形式化语言能否采用另一种更贴近自然数学的接口，让源码、验证过程和数学依赖关系都更容易被人理解、书写和参与？这不是寻找一个替代 Lean 的答案，而是为形式化语言增加一个值得验证的方向。

当然，Litex 也许不会成为唯一的道路，而且它不需要成为唯一的道路。Litex希望世界会因为数学而更好，数学世界会因为形式化语言而更好。我认为在Lean之外，有Litex这样的“非标准解法”是有长期价值的——同样只是个人判断，不是权威主张。

<details>
<summary><strong>作者的话</strong></summary>

我是沈嘉辰（Jiachen Shen），复旦大学数学博士生。Lean 让我看到，数学与编程可以在一门真实语言里相遇；Litex 则探索：形式化源码能否更贴近解数学题时的心流。

Litex 作者花了约两年时间，几乎天天从早到晚、完全志愿地做这个项目，没有物质回报。只希望借它交一些朋友，并为 Math for AI 多提供一种新思路。这是一个开源项目：[golitex](https://github.com/litexlang/golitex)；若您强烈反对 Litex 的存在或设计，欢迎认真讨论，但请不必乱喷。作者自认已尽所能把工作摊开给人看——真心希望 Math for AI 行业越来越好。

</details>

<a id="special-thanks"></a>

### 特别感谢

Litex 由沈嘉辰与 Litex 团队创建和维护。特别感谢 Wei Lin、Siqi Sun、
Peng Sun、Chenxuan Huang、Yan Lu、Sheng Xu、Keyao Zhu
和 Zhaoxuan Hong 对项目给予的支持与建议。

### 相关链接

1. 如果想直接试用例子，并查看 Litex 生成的输出和知识图谱，可以访问 [litexlang.com](https://litexlang.com)。

2. 如果关注内核实现，可以查看 [golitex 仓库](https://github.com/litexlang/golitex)。

注：当前仓库同时保留已检查成果、实验和未完成工作。*公开可见不等于宣称完成*；能力应以测试、带日期的状态、可信边界和已知限制为准。
