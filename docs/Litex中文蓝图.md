# Litex：让数学自我验证的形式化语言

文档由沈嘉辰创建和维护。

最后更新：2026 年 9 月 2 日。

官网页面: https://litexlang.com/doc/Litex中文蓝图

英文版: https://litexlang.com/doc/Litex_Blueprint

Litex 是一门基于集合论、事实导向、自下而上构建证明流的形式化语言。它把人类、AI 与验证器放进同一个闭环：人类给出数学意图，AI 提出或修复下一条事实，Litex 检查并返回依据或停止位置，由此循环积累可检查的数学知识。原理上，任何 Litex 代码都能编译成 Lean，并接入 Lean/Mathlib 生态。

> **Litex 是测试版（beta）的实验性爱好项目，可能存在边缘问题。**

<!-- 蓝图主线：AI 带来的推理过剩 → 科学对象 → 设计假设 → 可测成本 → 潜在能力影响 → 验证与理解的双重瓶颈 → 两种参与门槛 → 四项语言设计 → 数学实践中的定义与验证 → ToLean/adapter 接续 → 人类、AI 与 Litex 的端到端验证闭环 → 生态角色 → 从 AI for Math 走向 AI 时代的可信高效推理 → 成功标准 -->

<!--
Litex 定位四层检查（写作时逐层核对；面向不同受众可以调整强调重点，但不能混淆层级）：
- 科学对象：可检查知识如何被表示和逐步构造。
- 科学假设：事实导向表示与事务式交互是否构成新的形式语言范式。
- 科学结果变量：这种范式怎样影响人类与 AI 构造、理解、审核、修复和复用知识的成本，以及单位时间内能够可靠处理的候选推理量。
- 社会影响：以 AI for Math 为起点，降低进入可验证知识生产与审核的门槛，使验证能力有可能跟上 AI 产生候选推理的速度，并为 AI 时代更广泛的可信高效推理积累方法与基础设施。
写作边界：前三层是 Litex 的科学内核；第四层是潜在影响。不得用“从而”把未验证的科学结果写成已经实现的工具效果。
-->

## 目录

- [Litex 蓝图总览](#overview)
- [1. Litex 的数学基础：从最广为人熟悉的集合论出发](#set-theory)
  - [小例子：同一数学对象在不同的公理体系下的定义](#group-comparison)
- [2. 事实导向：把“什么成立”写进源码](#fact-oriented)
- [3. 自下而上：让已证明的事实推动后续证明](#bottom-up)
  - [小例子：同一条代数等式的两种写法](#two-directions)
- [4. Lean 兼容：为已覆盖路径提供独立复核](#compatibility)
- [Litex的数学实践：定义与验证](#mathematics-practice)
  - [完整例子：定义收敛并验证常数倍保持收敛](#convergence-example)
- [人类、AI 与 Litex 的端到端验证闭环](#interaction-loop)
- [从语言到生态：Litex 想扮演什么角色](#ecosystem-role)
- [总结](#conclusions)

<a id="overview"></a>

## Litex 蓝图总览

AI 正在迅速降低推理和科研探索的成本。但“看起来正确”的输出不等于可靠。从繁杂的AI推理中挖掘出真正有价值的、可信的结论，成为了科学家们和工程师们面临的挑战。这就是 **推理过剩、验证危机**。

**Litex 正在检验这条路线：一门基于集合论、事实导向、自下而上，并尝试与 Lean 兼容的形式化语言。** 用户写对象和事实，系统检查并返回依据或停止位置，并形成人类-AI-Litex的验证闭环。原理上，任何 Litex 代码都能编译成 Lean，并接入 Lean/Mathlib 生态。

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

## 2. 事实导向：把“什么成立”写进源码

任何数学证明都由“证明什么”和“怎么证”组成。阅读数学时，我们的心流通常是：看到书里的一句话，脑海里反应一下这句话为什么对，如果这句话被确认是正确的了，我们就在脑海里记忆下来这句话用于后续的推理。

Litex做的相当于就是把我们脑海的心流在机器中实现了。*用户写“证明什么”，内核寻找“怎么证”。*即内核帮我们思考了每句话为什么成立。同时，Litex把已经证明好的事实存储下来。当用户输入下一个数学语句后，Litex会从上下文中寻找依据，检查良定义性，并返回验证结果或停止位置。

> **事实导向最核心的人机分工是：用户写“我要证明什么”，Litex 寻找“这条事实可以怎样被验证”。**

关键选择、见证和估计仍由作者写；具体规则与等式对齐由内核寻找、记录。Litex 由事实触发局部搜索；结果都须可检查：Litex按关系、参数结构和上下文寻找内置规则、全称事实、具体事实或等式；搜索受支持范围限制，并非自由猜测。

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

匹配得到 `x := a`、`y := b`；内核仍检查二者属于实数且非负。形状只筛选候选，不跳过前提。Litex在验证完后会输出验证过程：

```text
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

#### 2. 用用户提供的全称事实匹配

候选也可来自用户证明或假设的全称事实：

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

这里 `prop` 给出“为正”的可复用数学接口；`forall` 建立一条可实例化的全称事实：任意大于 `10` 的实数都为正。后面的 `have a R: a > 10` 提供了具体前提，验证器便可以把这条全称事实实例化为 `a`，并接受 `$is_positive(a)`。Litex把它是如何验证上述源代码的过程会打印出来：

```text
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

#### 3. 用具体事实（concrete fact）和已知等式匹配

第三类来源是已有具体事实；等式可帮助匹配写法不同但相同的参数：

```litex
prop is_positive(x R):
    x > 0

forall a, b R:
    $is_positive(a)
    a = b
    =>:
        $is_positive(b)
```

我们让Litex输出它是如何验证上述源代码的过程。可以看到，`$is_positive(b)` 的验证过程是通过引用 `$is_positive(a)` 来完成的。这里用到了`a = b` 的等式来匹配参数。验证器会输出如下信息：

```text
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

> **设计空间中的位置。** 寻找局部证明依据并非 Litex 独有：
> [Lean `grind`](https://lean-lang.org/doc/reference/latest/The--grind--tactic/)、
> [Rocq `auto`](https://rocq-prover.org/doc/master/refman/proofs/automatic-tactics/auto.html)
> 和 [Isabelle/Isar](https://isabelle.in.tum.de/doc/isar-ref.pdf) 通过显式证明指令（tactic）或
> 证明方法（proof method）提供局部自动化；[Mizar](https://mizar.uwb.edu.pl/project/mizman.pdf)
> 有空验证（empty justification）；
> [ACL2](https://acl2.org/doc/index-seo.php?xkey=ACL2____DEFTHM) 可以在没有提示（hints）时
> 尝试证明定理事件（theorem event）；[Naproche](https://naproche.github.io/) 则用自动定理证明器
> 检查受控自然语言中的步骤。Litex 更具体地检验：普通数学陈述能否触发受当前上下文和规则限制的局部验证，并在通过后写回上下文、显示验证来源。

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

**Litex 源码 ✓ → 生成 Lean ✓ → Lean 内核 ✓ → Mathlib adapter ✓**

[在仓库中查看完整例子](https://github.com/litexlang/golitex/tree/main/showcases/litex_to_lean_mathlib_pipeline)。

这证明一条已覆盖路径完整走通，不代表所有 Litex 源码都能编译。

<details>
<summary><strong>Litex 到 Lean 的编译器如何工作</strong></summary>

总结来说，Litex到Lean的编译器的工作原理是，Litex 保留验证路径，把每个已支持步骤映射为 Lean 定理或证明构造，再组装成证明对象。Mathlib 对集合论数学的支持使这条路线自然可行。

实现它需要两层映射：验证路径映射为 Lean 证明构造；数学对象通过设计过的包装层映射为 Lean 表示，而非机械直译。这需要持续开发和验证；中介代码见 https://github.com/litexlang/golitex/blob/main/lean/Litex/Core.lean。

编译器有两个底层问题。其一是如何在 Lean/Mathlib 中表示 Litex 数学。同一对象常有多种等价写法，选择会长期影响 Mathlib 复用、Litex 扩展与生态协作；函数、集合、成员和良定义性必须采用一致、可持续的表示。

其二是把成功执行的信息变成 Lean 证明。搜索树的成功分支必须结构化返回规则、事实、对象、子证明和良定义性结果，并保留声明与作用域变化，使编译器能确定性重放路径，而非从显示文本重建或让 Lean 重新搜索。

</details>

Litex 不取代 Lean：前者提供数学写作接口，后者提供小内核复核与生态复用。已覆盖路径可形成可验证、可审核、可复用的流程；其余部分必须标明边界。

<a id="mathematics-practice"></a>

## Litex的数学实践：定义与验证

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

## 人类、AI 与 Litex 的端到端验证闭环

我们在这里端到端地创建一个人类、AI 与 Litex 的端到端验证闭环。这样的验证闭环适用于定义、定理、证明修复、可复用的数学接口、一章教材或一个多文件理论。它产出不只是 Litex 代码。一个成功的闭环会产生：

1. 由人类拥有的数学契约；
2. 按依赖顺序组织的数学发展；
3. 一份记录有验证器依据的尝试与决定的 JSON 记录；
4. 只包含已接受数学内容的物化 `.lit` 源码；
5. 诚实的验证与信任边界报告；以及
6. 在明确纳入范围且路径受支持时，一个经 Lean 内核检查的 Lean 产物。

```text
人类固定数学意图、约束与验收边界
                  ↓
AI 提出下一条 Litex 事实或证明块
                  ↓
Litex 检查良定义性与证明依据
       ├─ Committed（对读者：Accepted）
       │      ↓
       │  已接受上下文增长 → AI 提出下一块 ─────↗
       │
       └─ RolledBack（对读者：Stopped）
              ↓
          上下文保持不变
              ↓
      JSON 记录失败阶段与目标
              ↓
        AI 修复同一块 ─────────────────────────↗

连续 Committed 前缀
        ↓
物化为 .lit → 干净 Litex gate → trust / 边界审计
        ↓ 仅当路径受支持且实际生成
Generated.lean → Adapter.lean → Final.lean → Lean 内核
```

详细的闭环设计与实现见 [Litex 端到端验证闭环](https://litexlang.com/showcases)。

<a id="ecosystem-role"></a>

## 从语言到生态：Litex 想扮演什么角色

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

## 总结

Litex 以接近日常数学的语法和交互降低书写与审查门槛：用户写对象、条件和事实，系统返回依据或停止位置。

集合论让更多人能成为Litex专家，事实导向让Litex源码保存“什么成立”，自下而上积累已验证事实培养Litex用户直觉，Lean 兼容让Litex更严格并进入现有工具链。Litex不取代 Lean，而是检验更小的数学前端能否让更多人低成本生产、审核和修复可检查的数学。

如果形式语言未来十年内像 LaTeX或Python或数学本身 一样普及，它的入门成本也应接近 LaTeX。希望 Litex 能成为数学、AI 和工程师的可读推理前端、可信推理数据生产层和现有生态的接入层。

### 相关链接

1. 如果想直接试用例子，并查看 Litex 生成的输出和知识图谱，可以访问 [litexlang.com](https://litexlang.com)。

2. 如果关注内核实现，可以查看 [golitex 仓库](https://github.com/litexlang/golitex)。

注：当前仓库同时保留已检查成果、实验和未完成工作。*公开可见不等于宣称完成*；能力应以测试、带日期的状态、可信边界和已知限制为准。
