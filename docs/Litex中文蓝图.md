# Litex：让数学自我验证的形式化语言

文档由沈嘉辰创建和维护。

最后更新：2026 年 9 月 2 日。

官网页面: https://litexlang.com/doc/Litex中文蓝图

英文版: https://litexlang.com/doc/Litex_Blueprint

**Litex 是一门小而易读、事实导向的形式化语言，把数学推理转化为可检查、可追溯的数据，让人类、AI 与 Litex 能在同一闭环中共同推进。**

它以集合论为基础，自下而上构建证明流，并把人类、AI 与验证器放进同一个闭环：人类给出数学意图，AI 提出或修复下一条事实，Litex 检查并返回依据或停止位置，由此循环积累可检查的数学知识。原理上，任何 Litex 代码都能编译成 Lean，并接入 Lean/Mathlib 生态。

> **Litex 是测试版（beta）的实验性爱好项目，可能存在边缘问题。**

<!-- 蓝图主线：AI 带来的推理过剩 → 科学对象 → 设计假设 → 可测成本 → 潜在能力影响 → 验证与理解的双重瓶颈 → 两种参与门槛 → 四项语言设计 → 数学实践中的定义与验证 → ToLean/adapter 接续 → 人类、AI 与 Litex 的端到端知识生产闭环 → 生态角色 → 从 AI for Math 走向 AI 时代的可信高效推理 → 成功标准 -->

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
- [1. Litex 的数学基础：从最广为人熟悉的集合论出发](#set-theory)
- [2. 事实导向：把“什么成立”写进源码](#fact-oriented)
- [3. 自下而上：让已证明的事实推动后续证明](#bottom-up)
- [4. Lean 兼容：为已覆盖路径提供独立复核](#compatibility)
  - [小结：自下而上与自上而下互补](#summary-bottom-up-and-top-down)
- [5. Litex的数学实践：定义与验证](#mathematics-practice)
- [6. 人类、AI 与 Litex 的端到端知识生产闭环](#interaction-loop)
  - [小结：事实导向与自下而上的闭环优势](#summary-fact-oriented-bottom-up-loop)
- [7. 从语言到生态：Litex 想扮演什么角色](#ecosystem-role)
- [8. 总结](#conclusions)

<a id="overview"></a>

## 0. Litex 蓝图总览

AI 正在把我们从“推理稀缺”带入“推理充裕”的时代。过去，难点是提出足够好的猜想、推导和解法；现在，候选推理可以被大规模生成，但人类注意力、专家审核和可靠验证无法以同样的速度扩张。瓶颈正在从“能否产生一个看似合理的答案”，转向“能否把大量候选变成可检查、可理解、可复用的知识”。**推理过剩、验证稀缺，不是一时的失衡，而是 AI 时代知识生产正在形成的结构性条件。**

Litex 正是面向这种新条件的一项接口实验：一门基于集合论、事实导向、自下而上构建证明流的形式化语言。它检验这种表示与交互范式能否降低人类和 AI 构造、理解、审核、修复与复用可检查知识的成本。人类给出数学意图与验收边界，AI 提出或修复下一条事实，Litex 检查并返回依据或停止位置，由此形成持续生长的验证闭环。Litex 同时以 Lean 兼容为设计目标：当前编译器已能把部分受支持路径交给 Lean/Mathlib 独立复核，完整覆盖仍在推进中。

正确性只是危机的一半。形式化代码确实是正确的，却仍然难以理解。如何才能让信息的充盈转化为洞见的丰盈？AI For Math的社区总是在谈复杂性：证明长、表示繁、工具难、成果难消化。但我们很少追问这些理解成本为何产生，更少研究如何降低。这是 **理解所承担的复杂度税（the complexity tax on understanding）**。

复杂性不可能全部消失。有些属于数学本身；有些来自表示、证明证书和交互协议。结果的严格性和可读性之间存在张力。陶哲轩在 [2026 年 ICM 公开演讲](https://teorth.github.io/tao-web/slides/age-of-ai-icm-2026.pdf) 中强调了这一瓶颈对数学和其他领域的影响。*Litex 的目标是：在不降低严格性的前提下，降低形式化代码理解的复杂度税。*

从AI For Math出发，我们可以看到随着AI的发展，人们对可信推理的需求日益增长。从AI安全，到AI科学发现，只要有数学的地方，理论上形式化都能发挥作用。Litex的目标是：让更多人能参与形式化，让更多领域能注入形式化的严格性。避免即使AI确实生成了形式化代码，但由于难以理解，领域专家无法发现“证明正确，题目本身错了”的情况。

> **Litex 不只是为形式化专家而创造的工具，它的目标更是让更多人成为形式化专家，让各个行业都能注入形式化的严格性。**

Litex 的核心假设是：能否不降低标准，却让学生、领域专家和 AI 更容易写、读和修复可检查的数学？

全文沿四个相连问题展开：用户看见什么，源码保存什么，推理如何继续，结果如何独立复核。

1. **集合论对象**：用户先看见集合、元素、函数和关系，而非先管理承载类型。
2. **事实中心**：源码写“什么成立”；检查器寻找依据并检查良定义性。
3. **自下而上积累**：通过的事实进入上下文，供后续推理使用；这只是默认方向。
4. **Lean 复核**：已覆盖路径可翻译为 Lean 证明对象并由其内核检查；目前覆盖仍不完整。

全文通过比较 Litex 与 Lean 的写法，展示四项设计如何降低理解成本。最后讨论 Litex 在 AI For Math 生态中的角色，以及它如何帮助更多人参与形式化。如果您是Lean用户，可以先粗略地把Litex和Lean的默认流程理解成：

```text
Lean：命题 → 证明目标 → 证明指令与细化 → 证明对象 → 内核检查
Litex：对象和事实 → 内核检查并寻找依据 → 已验证事实扩展上下文
```

<details>
<summary><strong>两种门槛：从“理解数学”到“能够形式化”</strong></summary>

下面两个例子展示复杂度税的两个来源。它们不比较数学能力，只追问：从“我明白”到“我能形式化”，还差什么？

1. **工具使用门槛**：用户已经理解一个数学事实，却未必知道怎样把它写进形式系统。
2. **表达方式门槛**：形式系统中的数学写法，可能与我们熟悉的日常数学表达不同。

先看工具门槛。我们的数学问题是， `1 + 1 = 2`，问题只是能否把它交给形式系统。

Litex：

```litex
1 + 1 = 2
```

Lean：

```lean
import Mathlib

example : (1 : ℝ) + 1 = 2 := by norm_num
```

Lean 版本加载 Mathlib、开始例子、指定实数并调用数值化简。这些机制很有用，却不是事实本身。Litex 追问：用户理解事实后，能否直接写下它，由系统完成检查所需的工具工作？

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

Litex 仍检查 `x > 0`，但让它作为普通事实留在上下文中，源码仍写 `f(x)`。省去的是手工传递证据，对`f(x)`的两定义的检查由内核替你完成。

> **用户写数学，系统管理验证证据。条件足够时，Litex内核会帮你找到每段数学是如何证明的。**

目前AI For Math行业遇到的问题是：AI 可能生成通过 Lean 内核的代码，但实际命题少了条件、改变了量词或弱化了结论。Lean 内核没有出错；它正确检查了代码中的命题。错在形式陈述没有对齐数学意图。

理想状态下，Litex用户关注对象、条件、事实和结论，Litex 提供局部可追踪的反馈。*理解领域却并非证明助手专家的人，也能参与形式化，并知道系统检查到了哪里。*

> **这是设计方向，不是对当前语言、标准库或编译器已经完备的声明。**

</details>

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

<details>
<summary><strong>技术总结：类型判断与成员事实</strong></summary>

Lean 把数学组织成有类型的项：经过细化后，核心表达式由 `Γ ⊢ e : T` 形式的判断检查。冒号属于元语言层的类型判断，不是 Lean 对象语言中可与等式、序关系或定理事实并列累积的普通命题。表层重载和强制转换可以把相似写法细化成不同的核心项，但每个所得项都在一个确定类型下接受检查。

Litex 则把数学组织成对象与逐步增长的事实上下文。`e $in S` 是对象语言中的成员事实，与等式、序关系和其他谓词处于同一逻辑层。因此，同一对象可被证明属于多个无关或相互重叠的集合：成员关系是对象之间的关系，不是唯一内生赋值 `typeOf(e) = S`。

这不等于取消静态约束或推断。Litex 在接受表达式前仍会检查定义域、返回集合、结构字段和其他良定义性义务，并通过专用规则在证明中推出成员与载体事实。区别在于，这种推断向上下文增加 `e $in S` 一类事实，而不是推断一个决定对象身份的特权类型 `e : T`。

Lean的技术路线选择了 Dependent Type Theory（依赖类型论）作为基础。Litex 的技术路线选择了集合论作为基础。两者都能表达同样的数学，但在默认接口、源码风格和理解成本上有根本性差异。Lean选择了更抽象的数学公理体系，让它具备了通用的编程能力，也让它的内核更小更容易被检验。Litex的内核比Lean大数十倍，所以有专门的LitexToLean编译器把Litex代码翻译成Lean代码，并由Lean检查。二者没有高下之分，只是不同的技术路线选择。

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

`G.mul` 等字段路径按声明的结构载体检查，路径本身不会把群公理加入上下文。直接绑定 `G &Group<s>` 只自动打开一层；函数返回值或嵌套结构字段须用 `by struct def expression`，先验证结构归属再释放一层。后来单独得到的 `expression $in &Group<s>` 保持不透明。

Lean 当然也能脱离 Mathlib 自行定义群；这里比较的是默认体验，不是表达上限。“从头搭建”也不是无依赖：Litex 仍依赖内核、规则和标准库，外部库仍是重要加速器，只是不应成为表达边界。

群只是小示范。更强的检验是：小团队能否为现有库覆盖不足的领域建立可读、可扩展且边界清楚的接口。未来几何等领域库应以带日期的源码、验证结果、`trust` 边界和真实复用说明进展，而非预先宣称成功。

</details>

<details>
<summary><strong>设计空间中的位置：集合论式的表述并非 Litex 首创</strong></summary>

[Mizar 的数学库](https://wiki.mizar.org/library/) 基于塔斯基–格罗滕迪克（Tarski–Grothendieck）集合论；
[Lean](https://lean-lang.org/doc/reference/latest/The-Type-System/) 和
[Rocq](https://rocq-prover.org/doc/V9.2.0/refman/language/core/index.html) 向用户展示依赖类型论内核；
[Isabelle/HOL](https://isabelle.in.tum.de/website-Isabelle2024/dist/library/Doc/Isar_Ref/HOL_Specific.html)
使用多态高阶逻辑。

Litex 面向用户的命题语言大体具有一阶逻辑风格：原子关系或具名谓词通过受限的经典逻辑形式和量词组织。它偏好规范事实形态，命题和证明不能作为普通一等值任意组合。这只描述命题接口；验证器还会检查良定义性，并从定义、上下文和受支持规则中寻找依据。

在这个背景下，Litex 的问题更具体地落在面向用户的对象接口上：
一套小型、以成员关系为中心的集合论式表层，能否在不要求用户先管理类型
宇宙（universe）的前提下，覆盖有实质内容的数学？

</details>

<a id="fact-oriented"></a>

## 2. 事实导向：把“什么成立”写进源码

任何数学证明都由“证明什么”和“怎么证”组成。阅读数学时，我们的心流通常是：看到书里的一句话，脑海里反应一下这句话为什么对，如果这句话被确认是正确的了，我们就在脑海里记忆下来这句话用于后续的推理。

Litex做的相当于就是把我们脑海的心流在机器中实现了。*用户写“证明什么”，内核寻找“怎么证”。*即内核帮我们思考了每句话为什么成立。同时，Litex把已经证明好的事实存储下来。当用户输入下一个数学语句后，Litex会从上下文中寻找依据，检查良定义性，并返回验证结果或停止位置。

> **事实导向最核心的人机分工是：用户写“我要证明什么”，Litex 寻找“这条事实可以怎样被验证”。**

关键选择、见证和估计仍由作者写；具体规则与等式对齐由内核寻找、记录。Litex 由事实触发局部搜索；结果都须可检查：Litex按关系、参数结构和上下文寻找内置规则、全称事实、具体事实或等式；搜索受支持范围限制，并非自由猜测。

### 内核如何按事实形状寻找验证路径

这里用三组相同的数学事实对照两种典型界面。Lean 源码当然也包含陈述目标的 theorem statement，Litex 也允许显式指定定理和证明结构；差异在默认的注意力中心：

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
    x >= 0
    y >= 0
    =>:
        x + y >= 0
```

这条源码没有指定规则名称。目标 `x + y >= 0` 可拆成谓词 `>=` 与参数 `x + y`、`0`；内核据此筛选候选，匹配出两个非负前提，并继续检查类型和条件。

**Litex 输出｜解释 how**

```json
{
  "result": "success",
  "type": "universal fact",
  "line": 1,
  "statement": "forall x, y R:\n    x >= 0\n    y >= 0\n    =>:\n        x + y >= 0",
  "parameters": [
    "x",
    "y"
  ],
  "assumptions": [
    {
      "fact": "x $in R",
      "reason": "parameter definition"
    },
    {
      "fact": "y $in R",
      "reason": "parameter definition"
    },
    {
      "fact": "x >= 0",
      "reason": "forall premise",
      "inferred_facts": [
        "-1 * x <= 0"
      ]
    },
    {
      "fact": "y >= 0",
      "reason": "forall premise",
      "inferred_facts": [
        "-1 * y <= 0"
      ]
    }
  ],
  "conclusions": [
    {
      "statement": "x + y >= 0",
      "why_verified": {
        "type": "builtin rule",
        "rule": "0 <= a + b from known atomic facts 0 <= a and 0 <= b"
      }
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
  "result": "success",
  "type": "prop fact",
  "line": 14,
  "statement": "$is_positive(a)",
  "why_verified": {
    "type": "cite forall fact",
    "cite_source": {
      "line": 5
    },
    "cited_statement": "forall x R:\n    x > 10\n    =>:\n        $is_positive(x)"
  }
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
  "result": "success",
  "type": "universal fact",
  "line": 4,
  "statement": "forall a, b R:\n    $is_positive(a)\n    a = b\n    =>:\n        $is_positive(b)",
  "parameters": [
    "a",
    "b"
  ],
  "assumptions": [
    {
      "fact": "a $in R",
      "reason": "parameter definition"
    },
    {
      "fact": "b $in R",
      "reason": "parameter definition"
    },
    {
      "fact": "$is_positive(a)",
      "reason": "forall premise",
      "inferred_facts": [
        "a > 0"
      ]
    },
    {
      "fact": "a = b",
      "reason": "forall premise"
    }
  ],
  "conclusions": [
    {
      "statement": "$is_positive(b)",
      "why_verified": {
        "type": "cite prop fact",
        "cite_source": {
          "line": 5
        },
        "cited_statement": "$is_positive(a)"
      }
    }
  ]
}
```

</details>

<details>
<summary><strong>个人观察：命令式与声明式编程的类比</strong></summary>

粗略地说，编程语言有命令式与声明式编程两种风格。C、Rust 中常见的命令式代码强调“how”；Haskell 等函数式语言强调“what”。

有趣的是，Lean 本身是函数式、声明式语言，但 tactic proof 常读起来更像命令式程序。每条指令都改变当前 Goal。Litex 则把默认证明界面拉回“what”：作者写下一条应当成立的事实，验证器寻找“how”。

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

Litex 把四次重写反向写成等式链，从右端 `c * (d * f)` 经中间结果到达左端 `a * (b * g)`：

```litex
claim:
    ?forall a, b, c, d, g, f R:
        a * b = c * d
        g = f
        =>:
            a * (b * g) = c * (d * f)
    c * (d * f) = (c * d) * f = (a * b) * f = a * (b * f) = a * (b * g)
```

四个等号依次对应 `rw [mul_assoc]`、`rw [h]`、`rw [← mul_assoc]` 和 `rw [h']`，与 Lean 的指令逆序。Lean 指定下一步如何改写目标；Litex 写出沿途应当成立的事实，再由内核寻找相邻等式的依据。

</details>

<details>
<summary><strong>设计空间中的位置：前向证明并非 Litex 首创</strong></summary>

Mizar、Isar、ACL2 和 Naproche 已支持前向文本、定理累积或逐步检查，因此“自下而上”并非 Litex 独有。Litex 检验的是组合：普通事实自动触发局部验证，通过后扩展上下文；只有常规验证不足时才写显式证明结构。

</details>

<a id="compatibility"></a>

## 4. Lean 兼容：为已覆盖路径提供独立复核

Litex 可独立工作，拥有语法、运行时和验证内核；不编译成 Lean 也能检查良定义性与事实并提供反馈。Litex通常被认为更适合日常的数学写作和局部验证。

但在大型数学系统上，Lean有不可比拟的优势：Lean/Mathlib生态成熟、可复用的数学对象和定理库丰富、内核小而可审计。Litex需要和现有的形式化系统兼容，这样才能让用户在Litex中写的数学成果被更广泛地复用和验证。同时Lean社区也能从Litex中受益，Litex可以在一些数学方向为Lean提供更易读、更易写的数学接口。

*编译器还为 Litex 提供独立保障。* 当前 `src/` 下 Rust 源码接近 20 万行，含数百条规则；其可信实现面远大于 Lean 小内核，也更难完整审核。_目前Litex到Lean的编译器的覆盖尚未完全完成，但原理上这样的覆盖是可行的。我们预计2027年前会完成这一工作。_

<details>
<summary><strong>完整例子：证明“收敛数列乘常数后仍然收敛”，并将证明交给 Lean/Mathlib</strong></summary>

先说明我们要证明什么。设实数数列 `s` 收敛到 `a`，`c` 是任意实数。我们要证明新数列 `n ↦ c * s(n)` 收敛到 `c * a`：

`s(n) → a  ⟹  c * s(n) → c * a`

证明的核心是误差控制。给定任意 `epsilon > 0`，从 `s` 的收敛性中取误差 `epsilon / (abs(c) + 1)` 所对应的位置 `N0`。当 `n >= N0` 时，利用

`abs(c * s(n) - c * a) = abs(c) * abs(s(n) - a) <= (abs(c) + 1) * abs(s(n) - a) < epsilon`

即可得到新数列也收敛。因为 `abs(c) + 1` 始终为正，这种写法不需要另外讨论 `c = 0`。

这个例子不只展示最终定理，还展示同一份证明证据怎样从 Litex 交给 Lean/Mathlib。在当前已支持的编译路径上，Litex 首先检查源码中的定义、事实与证明证据；ToLean 再将已接受的定理编译为 Lean 代码，由 Lean 内核独立复核；最后，一层简短的手写 adapter 将生成定理导出为 Mathlib 的原生接口，例如 `Filter.Tendsto`。

`Litex 源码 → Litex 验证 → ToLean 编译 → Lean 内核复核 → 手写 adapter → Mathlib 定理`

下面沿着这条证据链，依次看每一层实际写什么。完整的 Litex 证明会在下文再次逐步解释。

#### 1. Litex 源码：定义收敛并证明常数倍仍然收敛

人类或 AI 在 Litex 中写下数学定义、条件和事实链。Litex 验证通过后，`converges_to_mul_const` 才会进入可供编译的已接受上下文。

<!-- litex:skip-test -->

```litex
# main.lit
prop is_eventually_close(s fn(n N) R, a R, epsilon R+, N0 N):
    forall n N:
        n >= N0
        =>:
            abs(s(n) - a) < epsilon

prop converges_to(s fn(n N) R, a R):
    forall epsilon R+:
        exist N0 N st {$is_eventually_close(s, a, epsilon, N0)}

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
                    abs(c * s(n) - c * a) = abs(c * (s(n) - a)) = abs(c) * abs(s(n) - a)
                    abs(c) * abs(s(n) - a) <= (abs(c) + 1) * abs(s(n) - a) < (abs(c) + 1) * (epsilon / (abs(c) + 1)) = epsilon
                    abs(fn(k N) R {c * s(k)}(n) - c * a) < epsilon
            by def $is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, N0)
    by def $converges_to(fn(n N) R {c * s(n)}, c * a)
```

#### 2. ToLean 生成代码：把已接受定理变成 Lean 证明对象

ToLean 根据 Litex 保存的验证依据生成定义、定理和证明项。下面是生成文件的结构化节选；包装参数和较长的证明体已省略，生成文件不由用户手改。

```lean
-- LitexGenerate.lean（由 ToLean 生成，节选）
namespace __Compiler_main

def is_eventually_close (...) : Prop := ...
def converges_to (...) : Prop := ...

theorem converges_to_mul_const :
    ∀ (s : (Litex.fnSet Litex.N Litex.R).Carrier) ...,
      converges_to (...) (...) := by
  -- 较长的生成证明体在此节选中省略。
  ...

end __Compiler_main
```

这段生成代码交给 Lean 时，Lean 内核检查最终证明对象，而不是信任 Litex 验证器给出的“成功”标签。

#### 3. 手写 adapter：调用生成定理并转换表示

adapter 不修改生成文件。它调用生成定理，再把 Litex 的数列、成员证据与收敛定义转换为 Mathlib 使用的表示。关键调用可以保持很短：

```lean
-- LitexToMathlib.lean（手写 adapter，节选）
import LitexGenerate

have generated :=
  __Compiler_main.converges_to_mul_const s sIn a aIn c cIn h
```

实际的表示桥接集中在一个可单独审核的定理中：

```lean
-- LitexToMathlib.lean（表示桥接，节选）
theorem tendsto_of_generated_convergesTo
    (s : LitexRealSequence)
    (a : ℝ)
    (h : __Compiler_main.converges_to s a) :
    Filter.Tendsto (toMathlibSequence s) Filter.atTop (nhds a) := by
  rw [Metric.tendsto_nhds]
  -- 从生成的收敛证据中取出 N，并转换成 Mathlib 的 eventually_atTop 证明。
  ...
```

#### 4. Mathlib 接口：结论成为 `Filter.Tendsto` 定理

完成桥接后，定理的结论已经使用 Mathlib 的数列极限接口；后续 Lean 代码可以按普通 `Filter.Tendsto` 定理复用它。

```lean
-- LitexToMathlib.lean（Mathlib-facing 定理，节选）
theorem tendsto_mul_const_from_generated (...) :
    Filter.Tendsto
      (toMathlibSequence (scaleSequence c s))
      Filter.atTop
      (nhds (c * a)) := by
  have generated :=
    __Compiler_main.converges_to_mul_const s sIn a aIn c cIn h
  exact tendsto_of_generated_convergesTo _ _ generated
```

这证明一条已覆盖路径完整走通，不代表所有 Litex 源码都能编译。折叠示例中的生成代码和 adapter 均为关键结构节选，省略号表示未展示的包装细节或证明体。

</details>

<details>
<summary><strong>Litex 到 Lean 的编译器如何工作</strong></summary>

总结来说，Litex到Lean的编译器的工作原理是，Litex 保留验证路径，把每个已支持步骤映射为 Lean 定理或证明构造，再组装成证明对象。Mathlib 对集合论数学的支持使这条路线自然可行。

实现它需要两层映射：验证路径映射为 Lean 证明构造；数学对象通过设计过的包装层映射为 Lean 表示，而非机械直译。这需要持续开发和验证；中介代码见 https://github.com/litexlang/golitex/blob/main/lean/Litex/Core.lean。

编译器有两个底层问题。其一是如何在 Lean/Mathlib 中表示 Litex 数学。同一对象常有多种等价写法，选择会长期影响 Mathlib 复用、Litex 扩展与生态协作；函数、集合、成员和良定义性必须采用一致、可持续的表示。

其二是把成功执行的信息变成 Lean 证明。搜索树的成功分支必须结构化返回规则、事实、对象、子证明和良定义性结果，并保留声明与作用域变化，使编译器能确定性重放路径，而非从显示文本重建或让 Lean 重新搜索。

</details>

Litex 不取代 Lean：前者提供数学写作接口，后者提供小内核复核与生态复用。已覆盖路径可形成可验证、可审核、可复用的流程；其余部分必须标明边界。

<a id="summary-bottom-up-and-top-down"></a>

### 小结：自下而上与自上而下互补

数学实践中，自下而上的事实积累与自上而下的目标分解并不是二选一，而是同时存在、相互校验的两种方向。Litex 与 Lean 的设计思路因此是互补的：Litex 让作者从对象、条件和已验证事实出发，逐步生长一条可读的证明流；Lean 则从明确目标出发，通过目标分解和证明项构造，把结果交给小内核独立检查。两者可以在同一条工作流中分工，而不必争论哪一种方向“更正确”。

从我的观察看，AI 在 *fact-oriented* 表达和自下而上的局部推进上往往表现得很自然，可能与其训练材料有关：互联网中的知识大多以事实、结论和局部推导的形式组织，模型从这些数据中学习到相应的模式。但这只是关于数据分布和模型行为的工作假设，不是对所有模型或任务的普遍结论。

同时，AI 的训练也围绕目标函数和奖励信号展开。这里的“奖励”不等同于 Transformer 架构本身；更准确地说，Transformer 提供表示与生成架构，训练过程再通过损失函数以及在某些阶段使用的偏好/奖励优化模型行为。因而，AI 未必天然具备稳定的、从第一性原理自下而上展开的推理能力；在许多任务中，它更容易从期望结果或评价信号反向组织一条看起来能够到达结果的路径。

因此，两种思维模式都很宝贵：自下而上适合积累可复用的局部事实、暴露中间依据；自上而下适合澄清目标、选择方向、压缩搜索空间。Litex 与 Lean 的连接，正可以把这两种方向放进同一条可检查的证据链，并让人类和 AI 在各自擅长的方向上协作。

<a id="mathematics-practice"></a>

## 5. Litex的数学实践：定义与验证

从形式化实践看，数学工作常在两个动作之间反复往返：一是**定义**对象、关系和可复用接口，建立一个领域的语言；二是**验证**这些定义与条件能够推出哪些事实。下面用一个完整例子把定义、量词、见证和估计放进同一条证明流。我们还是用Lean和Litex做对比。

> **Lean 证明指令：定理先给出最终证明目标 → 用户声明应当如何改写、分解或关闭它 → 信息视图显示还剩哪些证明目标 → 证明指令构造证明对象 → 内核检查该证明对象。**

我们定义数学分析中常见的`收敛`的概念：对任意正误差 `ε`，存在位置 `N`，使此后每项都足够接近极限；再证明 `{s(n)}` 收敛到 `a` 时，`{c * s(n)}` 收敛到 `c * a`。

```lean
import Mathlib

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ)
    (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  dsimp
  have εcpos : 0 < ε / |c| := by
    exact div_pos εpos acpos
  rcases cs (ε / |c|) εcpos with ⟨Ns, hs⟩
  use Ns
  intro n ngt
  calc
    |c * s n - c * a| = |c| * |s n - a| := by
      rw [← abs_mul, mul_sub]
    _ < |c| * (ε / |c|) :=
      mul_lt_mul_of_pos_left (hs n ngt) acpos
    _ = ε := mul_div_cancel₀ _ (ne_of_lt acpos).symm
```

Lean 先处理 `c = 0`，再缩小误差、取出 `Ns` 并完成估计；`by_cases` 分类，`rcases` 取见证，`calc` 写等式链。这种方式通用可组合，但初学者要同时跟踪数学和证明状态。

Litex源码的书写，更接近日常数学书写：

> **Litex：用户声明“什么应当成立” → 检查器寻找证明依据 → 通过的事实扩展当前上下文。**

对应代码先定义“最终足够接近”和“收敛”，再从原收敛性取得位置并为新数列构造见证：

```litex
# 1. 用 prop 定义“最终足够接近”：forall n，只要 n >= N0，=>: 后的距离界就成立。
prop is_eventually_close(s fn(n N) R, a R, epsilon R+, N0 N):
    forall n N:
        n >= N0
        =>:
            abs(s(n) - a) < epsilon

# 2. 收敛的意思是：forall 正误差 epsilon，都存在一个让上述 prop 成立的 N0。
prop converges_to(s fn(n N) R, a R):
    forall epsilon R+:
        exist N0 N st {$is_eventually_close(s, a, epsilon, N0)}

# 3. 把“s 收敛 =>: c * s 收敛”写成一个 thm。
thm converges_to_mul_const:
    ? forall s fn(n N) R, a, c R:
        $converges_to(s, a)
        =>:
            $converges_to(fn(n N) R {c * s(n)}, c * a)
    # 4. 先 claim 一个局部目标：forall epsilon，都要证明存在 N0。
    claim:
        ? forall epsilon R+:
            exist N0 N st {$is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, N0)}
        # 5. 为了给这个存在性找到见证，选择更小的正误差 epsilon / (abs(c) + 1)。
        abs(c) + 1 > 0
        epsilon / (abs(c) + 1) $in R+
        # 6. 原收敛性已经说这样的 K 存在，所以 obtain N0。
        obtain N0 from exist K N st {$is_eventually_close(s, a, epsilon / (abs(c) + 1), K)}
        # 7. 要完成新数列的存在性，就把同一个 N0 作为 witness 交出去。
        witness exist K N st {$is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, K)} from N0:
            # 8. 进入 forall n；把 n >= N0 放在 =>: 左边，右边证明距离界。
            forall n N:
                n >= N0
                =>:
                    abs(s(n) - a) < epsilon / (abs(c) + 1)
                    # 9. 沿事实链提出 abs(c)，再用 abs(c) <= abs(c) + 1 把误差压到 epsilon 以下。
                    abs(c * s(n) - c * a) = abs(c * (s(n) - a)) = abs(c) * abs(s(n) - a)
                    abs(c) * abs(s(n) - a) <= (abs(c) + 1) * abs(s(n) - a) < (abs(c) + 1) * (epsilon / (abs(c) + 1)) = epsilon
                    # 用 fn 写出的新数列，在 n 处需要的正是这个结论。
                    abs(fn(k N) R {c * s(k)}(n) - c * a) < epsilon
            # 10. by def is_eventually_close：由定义，上面的 forall 事实就是“最终足够接近”。
            by def $is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, N0)
    # 11. by def converges_to：再由定义，刚才的 forall / exist 结构就是收敛。
    by def $converges_to(fn(n N) R {c * s(n)}, c * a)
```

前两个 `prop` 定义：“最终足够接近”，什么叫“收敛”。随后 `obtain N0` 从原收敛性取出位置，`witness` 把它交给新数列；`epsilon / (abs(c) + 1)` 避免另分 `c = 0`，不等式链再把误差压到 `epsilon` 以下。

从这个例子可以看到，不同的形式化语言的源码风格是很不一样的。选择合适的语言用在合适的场景上，是非常重要的。

<a id="interaction-loop"></a>

## 6. 人类、AI 与 Litex 的端到端知识生产闭环

闭环的关键不只是让 AI 生成代码，而是让验证结果决定 AI 的下一步。人类给出数学意图、约束和验收边界；AI 提出下一条 Litex 事实；Litex 检查它是否良定义、是否具有足够的证明依据，并返回机器可读的结果。

`数学意图 → AI 候选 → Litex 检查 → Committed / RolledBack → 继续 / 修复`

`Committed` 的候选进入已接受上下文，AI 可以继续下一条事实；`RolledBack` 的候选不会改变上下文，AI 根据失败阶段、失败目标和验证依据修复当前候选。JSON 可以保存这些尝试与决定，但 JSON 记录本身不是证明。

<details>
<summary><strong>示例：Litex 怎样指导 AI 修复子群乘法</strong></summary>

**Human｜给出数学目标**

> 已知 `H` 是群 `G` 的一个子群。定义 `H` 上的乘法，使 `x, y ∈ H` 时，`group.mul(x, y)` 仍被看作 `H` 中的元素。

**AI｜提交第一份接口候选**

AI 最初通过此前定义的 `subgroup_carrier` 别名声明返回集合。现有 proof journal 没有保存这次候选的完整源码，因此这里不把它还原成逐字记录；journal 保存了决定性的验证结果：

> **输出边界：**下面的 JSON 是现有 proof journal 从当时 Litex 输出中保留的可读字段节选，不是稳定的输出 API。随着 Litex 演进，字段名称、嵌套结构和文字消息都可能变化；闭环真正依赖的是是否提交、最早失败位置和验证依据这些语义。

```json
{
  "attempt_id": "SS003A1",
  "result": "rejected_rolled_back",
  "failed_phase": "verify_well_definedness",
  "verifier_evidence": "Return value group.mul(x,y) was not inferred to belong to the cross-file subgroup_carrier."
}
```

上下文保持不变。AI 根据停止位置判断：数学定义不需要改变，需要调整的是返回集合的表达方式。

**AI｜只修复已经定位的接口问题**

第四次候选保持同一个函数值，直接把返回集合写成与 `subgroup_carrier` 定义相等的 `H`：

<!-- litex:skip-test -->
```litex
template<G nonempty_set, group &group::Group<G>, H power_set(G):
    $subgroup::is_subgroup(G, group, H)>:
    have fn subgroup_mul(
        x, y \subgroup_carrier<G, group, H>
    ) H = group.mul(x, y)
```

**Litex｜接受修复**

```json
{
  "attempt_id": "SS003A4",
  "result": "accepted",
  "verifier_evidence": "Outer try committed after declaring the return carrier as the definitionally equal H."
}
```

这条事实随后进入已接受上下文，AI 可以继续定义子群的单位元和逆元。这里展示的是一次真实交互，不意味着所有失败都能由 AI 自动修复。

</details>

同一个循环可以从一条事实扩展到一条定理、一个可复用接口、教材章节或多文件理论。连续提交的证明块可以物化为只含已接受数学的 `.lit` 源码；在明确纳入范围且编译路径受支持时，还可以继续生成由 Lean 内核检查的证明产物。

详细的闭环设计与实现见 [Litex 端到端验证闭环](https://litexlang.com/showcases)。

<a id="summary-fact-oriented-bottom-up-loop"></a>

### 小结：事实导向与自下而上的闭环优势

| 设计收益 | 在 human–AI–Litex loop 中的机制 | 带来的意义 | 边界 |
| --- | --- | --- | --- |
| 中间事实可复用 | 已验证事实进入上下文，成为后续证明的材料 | 即使最终目标失败，已接受的中间步骤仍可能用于其他证明、定义或接口 | 是否能复用取决于事实的范围、表达和后续需求 |
| 每轮试错成本更低 | 候选失败时事务回滚，只修复当前候选 | AI 不必从头重写整个证明，可以沿着上一次的状态继续 | 这是降低单轮修复成本的设计优势，不等于 AI 在所有任务上都更高效 |
| 错误不会污染上下文 | `RolledBack` 候选不会进入已接受事实集 | 错误尝试不会成为后续证明的错误前提 | 仍需审核命题本身是否符合数学意图 |
| 成功和失败都有解释 | 失败返回阶段、目标和验证依据；成功保留成立路径 | 人类可以告诉 AI “错在哪里”，也能告诉它“为什么这一步是对的” | 输出字段和文字可能随系统演进而变化，稳定的是这些语义 |
| 更容易对齐数学意图 | 人类提供目标、条件和验收边界；AI 提出局部事实 | 人类审核的不只是证明是否通过，也包括题目是否被正确表达 | Litex 不能自动替代人类判断数学意图 |
| 人类注意力得到重新分配 | 人类负责意图和边界，AI 负责候选探索，Litex 负责局部检查 | 人类不必逐行指导所有语法和搜索细节 | 关键定义、条件和最终判断仍需要人的参与 |
| 失败可以推动系统改进 | 失败被定位为表达、规则、标准库、内核或诊断问题 | 一次失败不仅是“没证明出来”，还可能成为语言和工具的改进线索 | 需要后续分类和验证，不能把每个失败都直接归因于内核 |
| 推理轨迹可以保存和恢复 | 提交事实、回滚位置和验证依据形成连续轨迹 | 可以从已接受前缀继续，也可以把轨迹用于审核、评估和未来的 AI 训练 | “有助于训练 AI”是数据潜力，不是已完成的性能证明 |
| 重要路径可以升级复核 | 已覆盖路径继续交给 Lean/Mathlib 独立检查 | Litex 提供易写、易修复的前端，Lean 提供额外的内核复核 | 只有当前已覆盖并成功编译的路径享有这层保障 |

因此，human–AI–Litex loop 的产物不只是最终证明，而是一条带有命题边界、提交状态、失败位置、验证依据和可复用中间事实的推理轨迹。Litex 的事实导向和自下而上设计，使这条轨迹能够被继续使用、定位修复、审核和改进。

<a id="ecosystem-role"></a>

## 7. 从语言到生态：Litex 想扮演什么角色

所有的设计合在一起，使 Litex 不只是一种语法，也希望成为人和 AI 共同生产、使用可检查推理的基础设施。

**Litex 面向人类与 AI：既是可读推理前端，也是可信推理数据生产层，并尝试通过 Lean/Mathlib 接入现有生态。** 它希望也服务于 AI、工程师和其他领域实践者。

这三个角色分别对应以下具体产物：

| 生态角色 | Litex 希望产生的实际成果 |
| --- | --- |
| 可读推理的前端 | 人可以直接审核的数学对象、条件、中间事实和结论 |
| 可信推理数据的生产层 | 经过机器检查的事实与验证来源、明确的停止边界，以及被显式标出的可信边界 |
| 现有生态的接入层 | 当前已支持源码路径对应的 Lean 证明对象，以及明确分离、由 AI 或人类编写的新增 Lean/Mathlib adapter |

优势区：

- **数学草稿本**：快速把日常推导变成可检查的数学。
- **形式化中间层**：连接自然语言数学与 Lean 等成熟证明系统。
- **新领域孵化器**：低成本试验定义、接口和小型领域库。
- **AI 证明训练场**：提供局部反馈、修复轨迹和失败分类。

劣势区：

- **成熟库复用**：大量依赖现成成果时，Lean/Mathlib 更强。
- **深层抽象工程**：复杂类型结构和大型理论体系目前更适合 Lean。
- **长期可信资产**：公共库的维护、审计、兼容与最终可信交付，Lean 更成熟。

代码量、定理数和数据集规模只是中间指标。关键是产物能否被人读懂、机器检查、后续复用，并在支持范围内进入工具链。更大地来说，Litex是否成功取决于有没有真的让更多的人和 AI 参与到原本只有少数形式化专家才能进入的验证闭环中。从AI For Math出发，到AI For Safe Reasoning，形式化语言可能会成为AI工程的基础设施。

<a id="reasoning-direction"></a>

<a id="conclusions"></a>

## 8. 总结

Litex 以接近日常数学的语法和交互降低书写与审查门槛：用户写对象、条件和事实，系统返回依据或停止位置。

集合论让更多人能成为Litex专家，事实导向让Litex源码保存“什么成立”，自下而上积累已验证事实培养Litex用户直觉，Lean 兼容让Litex更严格并进入现有工具链。Litex不取代 Lean，而是检验更小的数学前端能否让更多人低成本生产、审核和修复可检查的数学。

如果形式语言未来十年内像 LaTeX或Python或数学本身 一样普及，它的入门成本也应接近 LaTeX。希望 Litex 能成为数学、AI 和工程师的可读推理前端、可信推理数据生产层和现有生态的接入层。

数学是科学大厦深处看不见的骨架。我们相信，任何数学都可以被形式化，而形式化数学终将成为数学发展的未来。Litex 愿意成为其中的一块基石。

### 相关链接

1. 如果想直接试用例子，并查看 Litex 生成的输出和知识图谱，可以访问 [litexlang.com](https://litexlang.com)。

2. 如果关注内核实现，可以查看 [golitex 仓库](https://github.com/litexlang/golitex)。

注：当前仓库同时保留已检查成果、实验和未完成工作。*公开可见不等于宣称完成*；能力应以测试、带日期的状态、可信边界和已知限制为准。
