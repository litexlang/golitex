# Litex：让数学自我验证的形式化语言

文档由沈嘉辰创建和维护。

官网页面: https://litexlang.com/doc/Litex中文蓝图

英文版: https://litexlang.com/doc/Litex_Blueprint

> **Litex 是一个实验性爱好项目，仍处于测试版（beta）阶段。请预期会有边缘问题。**

<!-- 蓝图主线：推理过剩 → 验证与理解的双重瓶颈 → 理解所承担的复杂度税 → 两种参与门槛 → 人与 AI 的验证闭环 → 四项语言设计 → 数学实践中的定义与验证 → ToLean/adapter 接续 → 生态角色 → 成功标准 -->

## 目录

- [Litex 蓝图总览](#overview)
- [人类与 AI 的验证闭环](#interaction-loop)
- [1. 基于集合论：让数学对象保持可读](#set-theory)
  - [小例子：从共同基础搭建群及其数学接口](#group-comparison)
- [2. 事实导向：源码保存“什么成立”](#fact-oriented)
- [3. 自下而上：让已验证事实继续生长](#bottom-up)
  - [小例子：同一条代数等式的两种写法](#two-directions)
- [4. Lean 兼容：为已覆盖路径提供独立复核](#compatibility)
- [从四项设计到数学实践：定义与验证](#mathematics-practice)
  - [完整例子：定义收敛并验证常数倍保持收敛](#convergence-example)
  <!-- - [下一阶段：把 Litex 结果接到 Mathlib 风格的数学](#next-stage-pipeline) -->
- [从语言到生态：Litex 想扮演什么角色](#ecosystem-role)
- [总结](#conclusions)

<a id="overview"></a>

## Litex 蓝图总览

AI 正在迅速降低推理、证明和科研探索的成本。人和 AI 能在短时间内提出大量论证与猜想。但“看起来正确”不等于可靠。候选结论的增长已超过核对能力。这就是 **推理过剩、验证危机**。

正确性只是危机的一半。证明可以正确，却仍然难读、难讲、难接入现有理论。数学家和形式语言社区几乎每天都在谈复杂性：证明长、表示远、工具难、成果难消化。但我们很少追问这些理解成本为何产生，更少研究如何降低。这是 **理解所承担的复杂度税（the complexity tax on understanding）**。

复杂性不可能全部消失。有些属于数学本身；有些来自表示、证明证书和交互协议。AI 大量生成推理后，这个区分关系到两个目标：结果能否严格验证；人类能否理解、消化和复用它。

陶哲轩在 [2026 年 ICM 公开演讲](https://teorth.github.io/tao-web/slides/age-of-ai-icm-2026.pdf) 及其[配套文章](https://arxiv.org/abs/2608.16753)中展示了同一瓶颈。证明生成和验证可能领先于阐释、消化、社区接受与典范化。Litex 提出自己的研究假设：形式语言应同时扩展严谨验证与人类理解。这不是陶哲轩的主张。

教育、科研、工程和 AI 审核都需要形式化。形式化用机器可检的语言表达对象、条件和结论。要把 AI 创造力转为可信知识，这种能力不能只属于少数专家。

> **形式化语言的下一步，不只是让现有专家拥有更强的工具，也要让更多人成为专家。**

真正理解问题的人，应能表达、检查和修复推理，也能直接审核 AI 形式化；否则最懂问题的人反而被排除在验证之外。

**Litex 正在检验这条路线：一门基于集合论、事实导向、自下而上，并尝试与 Lean 兼容的形式化语言。** 用户写对象和事实，系统检查并返回依据或停止位置。Litex 降低的不是严谨标准，而是抵达严谨验证的工具门槛。

### 两种门槛：从“理解数学”到“能够形式化”

下面两个例子展示复杂度税的两个来源。它们不比较数学能力，只追问：从“我明白”到“我能形式化”，还差什么？

1. **工具使用门槛**：用户已经理解一个数学事实，却未必知道怎样把它写进形式系统。
2. **表达方式门槛**：形式系统中的数学写法，可能与我们熟悉的日常数学表达不同。

前者关心“先学多少工具才能写”，后者关心“写出的内容是否仍像原本的数学”。Lean 的机制支撑通用性、可组合性和成熟生态；Litex 探索另一种分工：条件仍须完整严格，更多证据与实现细节由系统管理。

先看工具门槛。用户已经知道 `1 + 1 = 2`，问题只是能否把它交给形式系统。

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

再看表达门槛。函数 `f` 只接受正实数，且已知 `x > 0`；我们只想写 `f(x)` 等于自身。Lean 的一种常见编码是：

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

**它表达的数学内容，其实只是函数值等于自身。**

Lean 用子类型（subtype）把值与其为正的证明绑定，因此调用时组合 `x` 与 `hx` 为 `⟨x, hx⟩`。设计精确通用，但读者须越过这层表示才能看到 `f(x)`。

Litex 仍检查 `x > 0`，但让它作为普通事实留在上下文中，源码仍写 `f(x)`。省去的是手工传递证据，不是数学条件。

> **用户写数学，系统管理验证证据。条件不能省略，证书不必手传。**

这改变的是机械工作的承担者：用户写清对象、条件和结论，系统管理证据。“更自然”不等于“少检查”。

AI 可能生成通过 Lean 内核的代码，但实际命题少了条件、改变了量词或弱化了结论。Lean 内核没有出错；它正确检查了代码中的命题。错在形式陈述没有对齐数学意图。

若形式陈述难读，最懂问题的领域专家就难发现“证明正确，题目却错了”。降低读写门槛既让更多人能写，也扩大了 AI 审核能力。

Litex 的核心假设是：能否不降低标准，却让学生、领域专家和 AI 更容易写、读和修复可检查的数学？

全文沿四个相连问题展开：用户看见什么，源码保存什么，推理如何继续，结果如何独立复核。

1. **集合论对象**：用户先看见集合、元素、函数和关系，而非先管理承载类型。
2. **事实中心**：源码写“什么成立”；检查器寻找依据并检查良定义性。
3. **自下而上积累**：通过的事实进入上下文，供后续推理使用；这只是默认方向。
4. **Lean 复核**：已覆盖路径可翻译为 Lean 证明对象并由其内核检查；目前覆盖仍不完整。

有了这些最基本的解释，两种默认流程可以先粗略地简化成：

```text
Lean：命题 → 证明目标 → 证明指令与细化 → 证明对象 → 内核检查
Litex：对象和事实 → 内核检查并寻找依据 → 已验证事实扩展上下文
```

理想状态下，用户关注对象、条件、事实和结论，Litex 提供局部可追踪的反馈。*理解领域却并非证明助手专家的人，也能参与形式化，并知道系统检查到了哪里。*

> **Lean 也支持其他编码和自动化方式；这里比较的是源码接口，而不是两种语言能否表达同一个命题。**

> **这是设计方向，不是对当前语言、标准库或编译器已经完备的声明。**

<a id="interaction-loop"></a>

## 人类与 AI 的验证闭环：写下事实，看见依据与停止边界

<!-- 这里之后加上，litex 怎么用 try 语句 和 proof journal 来，在增量与缓存验证 按 top-level block 缓存已经验证的前缀，只重跑受影响的依赖闭包。Chapter 9 的反馈周期应该从十几分钟降到几秒或几十秒。这还挺牛的-->

“容易写”还不够。面对大量推理，形式系统还应说明这一步为何接受、不能继续时停在哪里。Litex 的闭环是：**人类或 AI 写下事实；检查器返回依据或停止位置。** 用户据此补条件、拆步骤、改表达或继续前进。

例如 `A` 包含于 `B`，`B` 包含于 `c`，且 `x` 属于 `A`，自然可依次得到 `x` 属于 `B` 和 `c`：

```litex
forall A, B, c set, x A:
    A $subset B
    B $subset c
    =>:
        x $in B
        x $in c
```

首行声明三个集合和 `A` 的元素 `x`；`=>:` 前是条件，后是结论。运行器会记录每条事实的验证来源；下面只保留关键字段：

```text
{
  "statement": "x $in B",
  "proof": {
    "kind": "BuiltinRule",
    "diagnostic_label": "membership through a known direct set inclusion"
  }
}
{
  "statement": "x $in c",
  "proof": {
    "kind": "BuiltinRule",
    "diagnostic_label": "membership through a known direct set inclusion"
  }
}
```

`x $in A` 和 `A $subset B` 支持第一条结论。它通过后进入上下文，再与 `B $subset c` 支持第二条。源码保存“什么成立”，验证结果保存“为什么接受”。

现在故意加入一个无法得到的结论：声明集合 `d`，却不提供它与其他集合的关系，再要求 `x $in d`。运行器会把失败定位到第三条结论，并返回 `UnknownError`：

```text
"failed_prove": {
  "index": 3,
  "count": 3,
  "statement": "x $in d",
  "unknown_result": {
    "type": "atomic fact unknown",
    "goal": "x $in d"
  }
}
```

`unknown` 不表示命题为假，只表示当前条件和检查器支持的规则尚不能建立它。输出同时指出失败位置和目标，这就是“停止边界”。

这个 `forall` 作为整体提交，内部失败会使整条语句不进入环境；独立陈述或可回滚尝试则可保留成功前缀。Litex 不承诺解决所有证明搜索或总给出最小原因；它先让下一轮修正知道从哪里开始。

人类和 AI 因而共享同一节奏：提出事实，读取依据或停止位置，保留进展，再从边界继续。下面四部分会解释这个闭环如何成立。

<details>
<summary><strong>同一个例子：Lean 信息视图（Infoview）与 Litex 验证输出分别呈现什么</strong></summary>

在 Lean 中，同一证明从最终目标 `x ∈ c` 开始，由证明指令逐步化约到已有假设：

```lean
import Mathlib

example {α : Type} {A B c : Set α}
    (hAB : A ⊆ B) (hBc : B ⊆ c)
    {x : α} (hx : x ∈ A) :
    x ∈ c := by
  apply hBc
  apply hAB
  exact hx
```

信息视图显示每次证明指令执行后剩下的证明目标：

```text
进入 `by` 后：
⊢ x ∈ c

`apply hBc` 后：
⊢ x ∈ B

`apply hAB` 后：
⊢ x ∈ A

`exact hx` 后：
no goals
```

信息视图呈现“还需证明什么”；Litex 轨迹强调“已建立什么”“为何接受”，并标出停止事实。这里只比较默认工作流；Lean 也能写前向证明、保存中间结果，Litex 也有目标式结构。

</details>

<details>
<summary><strong>基本术语：形式化语言、证明目标、证明指令与内核</strong></summary>

- **形式化语言（formal language）**：语法和含义由明确规则规定，可由机器解析、检查；不等于行文正式，也不一定是通用编程语言。
- **证明助手（proof assistant）**：帮助用户表达证明、获得反馈并由机器检查的软件。Lean 也具有通用编程能力。
- **证明目标（Goal）与信息视图（Infoview）**：前者是当前待证命题；后者显示目标、局部变量和假设。
- **上下文（context）**：当前可用的变量、定义、假设和已验证事实；新事实会扩展它。
- **证明指令（tactic）**：操作目标的命令，描述“下一步怎样证明”，并非最终证明对象。
- **证明对象（proof term）与细化（elaboration）**：前者是机器可检查的完整证明；后者补全省略信息并生成它。
- **内核（kernel）**：Lean 中按基础规则核验证明对象的可信核心；复杂证明指令的结果仍须通过它。
- **内核/验证器（kernel/verifier）**：泛指负责检查的部分。Litex 内核还会搜索内置规则和上下文以验证事实，不能等同于 Lean 内核；其可信边界也更大。

</details>

<details>
<summary><strong>为什么 Litex 诞生在 AI 时代</strong></summary>

为提供不同的用户接口，Litex 验证器承担规则搜索、良定义性检查和证据管理。因此可信核心更大；这是明确的设计取舍。

过去，一个人很难同时承担语言设计、实现架构和大型验证器维护。AI 降低了实现成本：框架、语义和边界明确后，模型可快速生成候选实现，再由测试、审查和反例筛错。AI 不是正确性的来源，却让这种规模的小团队项目成为可能。

因此需要独立复核：Litex-to-Lean 把已记录路径编译为 Lean 证明对象。目前只有完整覆盖且实际通过 Lean 的路径获得这层保障；其他路径和 Litex 的可信实现面仍须审计。

</details>

<a id="set-theory"></a>
<a id="goal-2"></a>

## 1. 基于集合论：让数学对象保持可读

验证闭环从用户写下的内容开始，因此第一个问题是：源码先呈现什么？Litex 把集合、成员关系和集合间关系放在用户实际读写的表层，让集合问题直接写集合、子集和交集。系统仍检查对象和运算是否合法，但这些责任不必全部变成用户反复书写的代码。

例如，若 `s` 包含在 `t` 中，那么二者分别与同一集合 `u` 取交集后，前者仍包含在后者中：

```litex
forall s, t, u set:
    s $subset t
    =>:
        intersect(s, u) $subset intersect(t, u)
```

`s, t, u set` 声明三者为集合，`=>:` 前是条件，后是结论。日常证明是：任取 `intersect(s, u)` 中的元素，它属于 `s` 和 `u`；由 `s $subset t`，它也属于 `t`，所以属于 `intersect(t, u)`。源码直接呈现原命题，内核则沿交集定义和成员传递检查这条路径。

<details>
<summary><strong>完整对比：同一条集合论命题在 Lean 中如何展开</strong></summary>

下面是《Mathematics in Lean》集合论章节中的 Lean 版本：

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

Litex 让用户直接面对集合和成员关系，并为成员、子集与交并集提供直接语法和路径。元素范围仍存在，只是更多表达为成员事实，而非先建立类型论载体。

差异不在于“短代码更强”：Lean 也能用短证明或自动化完成它；这里刻意保留教材的展开路径。真正的区别是默认接口：Lean 先赋予集合类型论载体，再构造证明；Litex 直接识别和检查常见集合论事实。

</details>

直接的表层不等于取消约束。函数定义域和返回集合、结构字段，以及运算能否作用于给定对象，仍须通过良定义性检查，只是条件尽量写在数学本来出现的位置。`template` 可描述随载体、参数或假设变化的对象族，但只是受控索引机制；Litex 不因此自称拥有完整依赖类型论。

函数经过检查的契约——参数域、返回集合和调用条件——还能复用。验证器检查实参、推出返回值所属集合，并把事实传给外层调用。例如有 `f : A → B`、`g : B → C` 和 `a ∈ A` 后，可直接写 `g(f(a))`；系统检查 `f(a)` 能否作为 `g` 的输入。责任没有消失，省去的是反复抄写。

群、环等结构也沿用这种分工：载体与运算范围必须明确；Lean 默认以类型和函数组织，Litex 默认以集合、成员和集合上的运算组织。价值不只在代码更短，更在读者能从形式文本中认出原来的数学结构。

<details>
<summary><strong>AI 生成数学中的规格对齐</strong></summary>

证明助手能判断证明是否建立了实际编码的命题，却不能仅靠内核判断该命题是否符合作者意图。AI 产物可能内部正确，却只证明特例、改变定义或论域、弱化结论。这不是逻辑失效，而是意图与规格错位。

AI 越强，越需要作者或领域专家认出原意。若类型论抽象、细化、类型类和库接口使原命题提出者读不懂形式表达，内核接受可能只会增强对错误命题的信心。

Litex 让定义域、条件、中间事实和结论以接近日常数学又机器可检的形式留在源码中。它不能保证定理选对了，但希望懂数学的人能直接审查，并在验证后比较、重组文本，识别新结构。

**责任分工是：AI 生成形式化，内核检查它声称的命题，人类确认该命题就是原意。Litex 把最后一步视为核心要求。**

</details>

<a id="group-comparison"></a>

<details>
<summary><strong>小例子：从共同基础搭建群及其数学接口</strong></summary>

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

结构规律不会无条件出现；Litex 先确认结构归属和当前作用域。

<details>
<summary><strong>实现说明：结构（`struct`）事实的释放边界</strong></summary>

`G.mul` 等字段路径按声明的结构载体检查，路径本身不会把群公理加入上下文。直接绑定 `G &Group<s>` 只自动打开一层；函数返回值或嵌套结构字段须用 `by struct def expression`，先验证结构归属再释放一层。后来单独得到的 `expression $in &Group<s>` 保持不透明。

</details>

Lean 当然也能脱离 Mathlib 自行定义群；这里比较的是默认体验，不是表达上限。“从头搭建”也不是无依赖：Litex 仍依赖内核、规则和标准库，外部库仍是重要加速器，只是不应成为表达边界。

群只是小示范。更强的检验是：小团队能否为现有库覆盖不足的领域建立可读、可扩展且边界清楚的接口。未来几何等领域库应以带日期的源码、验证结果、`trust` 边界和真实复用说明进展，而非预先宣称成功。

</details>

> **设计空间中的位置。** 集合论式的表述并非 Litex 首创：
> [Mizar 的数学库](https://wiki.mizar.org/library/) 基于塔斯基–格罗滕迪克（Tarski–Grothendieck）集合论；
> [Lean](https://lean-lang.org/doc/reference/latest/The-Type-System/) 和
> [Rocq](https://rocq-prover.org/doc/V9.2.0/refman/language/core/index.html) 向用户展示依赖类型论内核；
> [Isabelle/HOL](https://isabelle.in.tum.de/website-Isabelle2024/dist/library/Doc/Isar_Ref/HOL_Specific.html)
> 使用多态高阶逻辑。
>
> Litex 面向用户的命题语言大体具有一阶逻辑风格：原子关系或具名谓词通过受限的经典逻辑形式和量词组织。它偏好规范事实形态，命题和证明不能作为普通一等值任意组合。这只描述命题接口；验证器还会检查良定义性，并从定义、上下文和受支持规则中寻找依据。
>
> 在这个背景下，Litex 的问题更具体地落在面向用户的对象接口上：
> 一套小型、以成员关系为中心的集合论式表层，能否在不要求用户先管理类型
> 宇宙（universe）的前提下，覆盖有实质内容的数学？

<a id="fact-oriented"></a>
<a id="workflow"></a>

## 2. 事实导向：源码保存“什么成立”

“事实导向”不是说证明过程不重要，而是重新分工：源码保存对象、条件和应当成立的事实；内核寻找并记录局部依据。用户仍提供有数学内容的中间步骤，只是不必把每一步都写成操作证明状态的命令。

前面的集合包含和群结构已给出两个小版本：用户直接写下希望成立的对象关系或结构事实，内核再寻找局部依据。这里先把这种分工本身讲清楚；定义、量词、见证和连续估计如何组合，将在四项设计之后用一个完整收敛例子展示。

<a id="goal-1"></a>
### 为什么普通事实不需要名字，也不需要证明指令？

像 `a + b >= 0` 这样的普通事实不必逐一命名，也不必逐行指定证明指令、库定理或改写方向。用户直接写当前需要的数学事实，让内核从上下文和受支持规则中找依据。

> **事实导向最核心的人机分工是：用户写“我要证明什么”，Litex 寻找“这条事实可以怎样被验证”。**

关键选择、见证和估计仍由作者写；具体规则与等式对齐由内核寻找、记录。Lean 由用户指导细化，Litex 由事实触发局部搜索；结果都须可检查。

经典定理、库接口和长期依赖仍可命名为 `thm`，再用 `release thm` 或 `by thm ... => fact` 取结论；临时判断不必都命名。

内核按关系、参数结构和上下文寻找内置规则、全称事实、具体事实或等式；搜索受支持范围限制，并非自由猜测。

<details>
<summary><strong>展开：内核如何按事实形状寻找验证路径</strong></summary>

#### 1. 用内置规则匹配事实形状

简单判断可拆成“谓词 + 参数”。例如：

```text
a + b >= 0
```

其谓词是 `>=`，参数是 `a + b` 和 `0`；左侧外形为加法，右侧为零。内核可据此筛选规则，无须知道事实名称。

例如：

```litex
have a R = 1
have b R = 2

a + b >= 0
```

目标形状使内核尝试以下非负性规则：

```text
forall x, y R:
    x >= 0
    y >= 0
    =>:
        x + y >= 0
```

匹配得到 `x := a`、`y := b`；内核仍检查二者属于实数且非负。形状只筛选候选，不跳过前提。

#### 2. 用用户提供的全称事实匹配

候选也可来自用户证明或假设的全称事实：

```litex
abstract_prop p(x)

trust forall a R:
    $p(a)

$p(1)
```

面对 `$p(1)`，内核找到 `$p(a)`，把 `a` 匹配为 `1`，再检查 `1 $in R`，从而验证目标。

`abstract_prop` 声明无定义谓词。`trust` 接受未经验证的事实并警告；含它的成果不完全可检查。此处仅用来展示匹配机制。

#### 3. 用具体事实（concrete fact）和已知等式匹配

第三类来源是已有具体事实；等式可帮助匹配写法不同但相同的参数：

```litex
abstract_prop q(x)

forall a R:
    $q(a)
    a = 1
    =>:
        $q(1)
```

验证 `$q(1)` 时，上下文的 `a = 1` 使 `$q(a)` 可沿等式运输为目标。

</details>

### 小结：把“证明什么”写进源码，把“怎么证明”交给内核

用户写结论，内核从规则、事实和等式中找依据。来源被记录，搜索受限；源码保留推理主线，轨迹补充机器依据。

<details>
<summary><strong>个人观察：声明式与命令式的类比</strong></summary>

借用不严格的类比：声明式强调“要什么”，命令式强调“怎么做”。Litex 更接近前者，普通事实无须先命名再引用，因而减少名称与依赖传递。Lean 本身是函数式语言；这里只说其证明指令交互会逐步改变状态，不是严格分类或优劣判断。

</details>

> **设计空间中的位置。** 寻找局部证明依据并非 Litex 独有：
> [Lean `grind`](https://lean-lang.org/doc/reference/latest/The--grind--tactic/)、
> [Rocq `auto`](https://rocq-prover.org/doc/master/refman/proofs/automatic-tactics/auto.html)
> 和 [Isabelle/Isar](https://isabelle.in.tum.de/doc/isar-ref.pdf) 通过显式证明指令（tactic）或
> 证明方法（proof method）提供局部自动化；[Mizar](https://mizar.uwb.edu.pl/project/mizman.pdf)
> 有空验证（empty justification）；
> [ACL2](https://acl2.org/doc/index-seo.php?xkey=ACL2____DEFTHM) 可以在没有提示（hints）时
> 尝试证明定理事件（theorem event）；[Naproche](https://naproche.github.io/) 则用自动定理证明器
> 检查受控自然语言中的步骤。Litex 更具体地检验：普通数学陈述能否触发受当前上下文和规则限制的局部验证，并在通过后写回上下文、显示验证来源。

<a id="goal-3"></a>
<a id="bottom-up"></a>

## 3. 自下而上：让已验证事实继续生长

事实通过后会加入上下文，成为后续推理资源。证明从已知条件建立局部结果，再逐步支持结论；这就是“自下而上”。

Litex 支持**声明式证明，默认主要采用前向推理**：从已知条件推出新事实，源码陈述结果，而非逐条命令系统改变状态。

推理单位是“上下文中的下一条事实”，而非每行必须推进的活跃目标。作用域内定义良好且有充分支持的陈述会被接受、保存并触发适用规则；不同分支也可先发展再汇合。

Lean 的典型交互则向后、自上而下：先固定目标，再把它分解为由假设或定理解决的子目标，最后组装证明对象。

Lean 常问“怎样把目标化约成已知条件”；Litex 常问“由已知条件能建立什么事实？”差异在默认方向，不在逻辑标准。

> 把证明想成搭乐高：Lean 通常从成品反向拆出缺少的部件；Litex 通常从已有积木向前拼接。比喻只说明默认方向，不表示 Litex 标准更宽松，也不表示两者只能单向工作。

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

独立陈述通过后可形成已验证前缀，下一条 `unknown` 标出修正位置；但同一复合语句内部失败时，不会只写入一半。

便利有可信成本：数百条内置和推理规则把部分脚本工作移入验证器，责任只是转移。Litex 因而记录验证路径，并把已覆盖路径交给可信边界更小的 Lean 内核复核。

<details>
<summary><strong>设计空间中的位置：前向证明并非 Litex 首创</strong></summary>

Mizar、Isar、ACL2 和 Naproche 已支持前向文本、定理累积或逐步检查，因此“自下而上”并非 Litex 独有。Litex 检验的是组合：普通事实自动触发局部验证，通过后扩展上下文；只有常规验证不足时才写显式证明结构。

</details>

第四项设计因此是：把验证结果交给 Lean，而非只要求用户相信 Litex。

<a id="compatibility"></a>

## 4. Lean 兼容：为已覆盖路径提供独立复核

Litex 可独立工作，拥有语法、运行时和验证内核；不编译成 Lean 也能检查良定义性与事实并提供反馈。

“Lean 数学前端”指 Litex-to-Lean 把已支持路径翻译成 Lean 证明对象并接入其生态。Litex 提供内容与接口经验，Lean 小内核和 Mathlib 帮助复核与复用；两者互补而非取代。

Litex 的事实优先接口聚焦数学对象和局部反馈；Lean 的细化、类型类、命名空间与指令支撑通用编程和大型库。Litex 提供入口，不重做 Lean 的成熟生态。

*编译器还为 Litex 提供独立保障。* 当前 `src/` 下 Rust 源码接近 20 万行，含数百条规则；其可信实现面远大于 Lean 小内核，也更难完整审核。

完整编译并通过 Lean 的路径会获得强而相对独立的证据。这不能证明 Litex 全部实现正确，却减少对其大型实现的单一依赖。

_这仍是实现目标，并非测试版已全面具备。编译器只覆盖部分对象、语句和路径；未完整编译并通过 Lean 的结果不能声称获得这层保障。_

<details>
<summary><strong>Litex 到 Lean 的编译器如何工作</strong></summary>

生态复用和独立复核指向同一技术路线：Litex 保留验证路径，把每个已支持步骤映射为 Lean 定理或证明构造，再组装成证明对象。Mathlib 对集合论数学的支持使这条路线自然可行。

实现它需要两层映射：验证路径映射为 Lean 证明构造；数学对象通过设计过的包装层映射为 Lean 表示，而非机械直译。这需要持续开发和验证；中介代码见 https://github.com/litexlang/golitex/blob/main/lean/Litex/Core.lean。

可执行的 [pipeline](../showcases/litex_to_lean_mathlib_pipeline/showcase1/README.md) 展示递归 `StmtResult` 证据、生成的 Lean 证明、外部 adapter 及其 Mathlib 消费者；实现导航和门禁由该 showcase 维护。

以下已验证定理说明证据映射和生态接口：

```litex
thm litex_real_add_comm:
    ? forall a, b R:
        a + b = b + a
```

第一层 Lean 接口是编译器的规范定理，保留 Litex 分类和验证证据：

```text
∀ {α β : Type} (a : α) (ha : Litex.In a Litex.R)
  (b : β) (hb : Litex.In b Litex.R),
  Litex.Same
    ((Litex.In.rep a ha : ℝ) + (Litex.In.rep b hb : ℝ))
    ((Litex.In.rep b hb : ℝ) + (Litex.In.rep a ha : ℝ))
```

编译器止于源码拥有的声明，不额外发明普通 Lean 推论：

```text
theorem litex_real_add_comm (a b : ℝ) : a + b = b + a
```

因为 `.lit` 文件没有该声明。“只翻译源码声明”使定理名、陈述和证明路径都可追溯。

普通 Mathlib 接口由 AI 或人类在独立的非生成模块中编写。adapter 可导入生成模块，但自行负责新增陈述和证明；编译器不把 API 设计或新数学藏在翻译中。

**互操作性有两个独立产物：ToLean 提供可由内核检查的源码翻译；外部 adapter 提供新增 Lean/Mathlib 接口，不能与编译器输出混淆。**

编译器有两个底层问题。其一是如何在 Lean/Mathlib 中表示 Litex 数学。同一对象常有多种等价写法，选择会长期影响 Mathlib 复用、Litex 扩展与生态协作；函数、集合、成员和良定义性必须采用一致、可持续的表示。

其二是把成功执行的信息变成 Lean 证明。搜索树的成功分支必须结构化返回规则、事实、对象、子证明和良定义性结果，并保留声明与作用域变化，使编译器能确定性重放路径，而非从显示文本重建或让 Lean 重新搜索。

</details>

Litex 不取代 Lean：前者提供数学写作接口，后者提供小内核复核与生态复用。已覆盖路径可形成可验证、可审核、可复用的流程；其余部分必须标明边界。

<a id="mathematics-practice"></a>

## 从四项设计到数学实践：定义与验证

从形式化实践看，数学工作常在两个动作之间反复往返：一是**定义**对象、关系和可复用接口，建立一个领域的语言；二是**验证**这些定义与条件能够推出哪些事实。前面的群与代数等式只是局部切片；下面用一个完整收敛例子把定义、量词、见证和估计放进同一条证明流。

<a id="convergence-example"></a>

<details>
<summary><strong>完整例子：定义收敛并验证常数倍保持收敛</strong></summary>

Lean 默认从待证目标开始。用户用证明指令改写、分解或关闭它，系统构造完整证明，再交给内核检查。这让用户能精确控制展开过程。

> **Lean 证明指令：定理先给出最终证明目标 → 用户声明应当如何改写、分解或关闭它 → 信息视图显示还剩哪些证明目标 → 证明指令构造证明对象 → 内核检查该证明对象。**

例子定义收敛：对任意正误差 `ε`，存在位置 `N`，使此后每项都足够接近极限；再证明 `{s(n)}` 收敛到 `a` 时，`{c * s(n)}` 收敛到 `c * a`。

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

Lean 先处理 `c = 0`，再缩小误差、取出 `Ns` 并完成估计；`by_cases` 分类，`rcases` 取见证，`calc` 写等式链。这种方式通用可组合，但初学者要同时跟踪数学和证明状态。日常书写更常：

1. 写下对象、定义和条件；
2. 看到一个熟悉的模式；
3. 使用已经知道的事实、定义或计算，写出下一条事实；
4. 让这条事实成为后续推理的上下文。

Litex 尝试把这种顺序变成默认逻辑：用户写事实，检查器寻找依据，通过后加入上下文。

> **Litex：用户声明“什么应当成立” → 检查器寻找证明依据 → 通过的事实扩展当前上下文。**

对应代码先定义“最终足够接近”和“收敛”，再从原收敛性取得位置并为新数列构造见证：

```litex
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

前两个 `prop` 建立领域语言：什么叫“最终足够接近”，什么叫“收敛”。随后 `obtain N0` 从原收敛性取出位置，`witness` 把它交给新数列；`epsilon / (abs(c) + 1)` 避免另分 `c = 0`，不等式链再把误差压到 `epsilon` 以下。这个例子把两种数学工作放在一起：先定义可复用接口，再验证它能推出新的事实。事实导向改变的是接口，不是删去数学内容。

</details>

<!--
<a id="next-stage-pipeline"></a>

### 下一阶段：把 Litex 结果接到 Mathlib 风格的数学

这个收敛例子目前展示的是 Litex 如何定义数学接口、如何验证数学事实。下一阶段更完整的蓝图证据，应把同一案例继续走完以下链路：

1. 人类或 AI（未来也可以由 Litex skill 约束工作流）写出 Litex 定义和定理；
2. Litex 验证源码，并把实际采用的验证路径保存在结构化结果中；
3. ToLean 只把源码拥有的声明及其证据编译成可由 Lean 内核检查的规范定理，不额外发明 Mathlib API；
4. 独立的 AI 或人类 adapter 导入生成模块，引用生成定理，通过已经证明的 wrapper/unwrap 桥梁取得 Mathlib 原生对象或结论，再继续证明真正面向下游的问题。

这里必须区分“已经有的架构”与“下一阶段的完整示例”。当前的[分层 showcase](../showcases/litex_to_lean_mathlib_pipeline/showcase1/README.md)已经把 Litex 源码、生成 Lean、外部 adapter 和下游消费者分成独立产物；但其中的 adapter 仍独立重建了一部分原生数学，并不是“直接引用生成定理再 unwrap 出目标定理”的完整证据。等这条消费路径能够以真实源码、生成文件和 Lean 内核门禁端到端运行后，蓝图再附上对应代码及 AI 使用 Litex skill 的工作流，才不会把路线图写成已经实现的能力。
-->

<a id="ecosystem-role"></a>

## 从语言到生态：Litex 想扮演什么角色

四项设计合在一起，使 Litex 不只是一种语法，也希望成为人和 AI 共同生产、使用可检查推理的基础设施。

**Litex 面向人类与 AI：既是可读推理前端，也是可信推理数据生产层，并尝试通过 Lean/Mathlib 接入现有生态。** 它希望也服务于 AI、工程师和其他领域实践者。

这三个角色分别对应以下具体产物：

| 生态角色 | Litex 希望产生的实际成果 |
| --- | --- |
| 可读推理的前端 | 人可以直接审核的数学对象、条件、中间事实和结论 |
| 可信推理数据的生产层 | 经过机器检查的事实与验证来源、明确的停止边界，以及被显式标出的 `trust` 与其他可信边界 |
| 现有生态的接入层 | 当前已支持源码路径对应的 Lean 证明对象，以及明确分离、由 AI 或人类编写的新增 Lean/Mathlib adapter |

“可信推理数据”不表示所有输出已获成熟证明助手同等级保障，而是携带检查结果、来源和边界。规则、`trust` 与实现仍须审计；只有完整编译并通过 Lean 的路径才获额外小内核复核。覆盖面与 adapter 生态仍在扩展。

代码量、定理数和数据集规模只是中间指标。关键是产物能否被人读懂、机器检查、后续复用，并在支持范围内进入工具链。

<a id="conclusions"></a>

## 总结

Litex 以接近日常数学的语法和交互降低书写与审查门槛：用户写对象、条件和事实，系统返回依据或停止位置。

集合论保持对象可读，事实导向保存“什么成立”，自下而上积累已验证事实，Lean 兼容复核已覆盖路径。它们不取代 Lean，而是检验更小的数学前端能否让更多人低成本生产、审核和修复可检查的数学。

如果形式语言未来十年内像 LaTeX 一样普及，它的入门成本也应接近 LaTeX。这是长期标准。它不意味着深刻数学、完整形式化或掌握证明助手会变得轻松。

**Litex 的成功，不在于写了多少 Litex 代码，而在于它能否把可读推理转化为可用的、可兼容到现有形式化语言系统的成果，并真正服务于数学、AI、工程和其他领域。**

评价 Litex 应看结果：人能否审核意图；人和 AI 能否根据反馈继续；事实能否跨项目复用；已支持路径能否进入 Lean/Mathlib；真实任务是否采用这些产物。产量不能单独证明成功。

若路线成立，它会先降低门槛，再让可读文本成为可检查、可复用的成果。更深的数学理解与发现是长期可能，不是语言设计已经兑现的结论。

### 相关链接

1. 如果想直接试用例子，并查看 Litex 生成的输出和知识图谱，可以访问 [litexlang.com](https://litexlang.com)。

2. 如果关注内核实现，可以查看 [golitex 仓库](https://github.com/litexlang/golitex)。

注：当前仓库同时保留已检查成果、实验和未完成工作。*公开可见不等于宣称完成*；能力应以测试、带日期的状态、可信边界和已知限制为准。

<!-- 蓝图主线：验证危机 → 两种参与门槛 → 人与 AI 的验证闭环 → 四项语言设计 → 数学实践中的定义与验证 → ToLean/adapter 接续 → 生态角色 → 成功标准 -->
