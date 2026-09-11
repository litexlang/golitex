# Litex：让数学自我验证的形式化语言

文档由沈嘉辰创建和维护。

最后更新：2026 年 9 月 8 日。

官网页面: https://litexlang.com/doc/Litex中文蓝图

英文版: https://litexlang.com/doc/Litex_Blueprint


*Litex是一门易学易用的形式化语言。它以集合论为基础，自下而上构建证明流，并把人类、AI 与验证器放进同一个闭环：人类给出数学意图，AI 提出或修复下一条事实，Litex 检查并返回依据或停止位置，由此循环积累可检查的数学知识。原理上，任何 Litex 代码都能编译成 Lean，并接入 Lean/Mathlib 生态，Litex到Lean的编译器预计2026年底完成。*

> **Litex 是测试版（beta）的实验性爱好项目，可能存在边缘问题。**

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
- [1. Litex 的数学基础：从最广为人熟悉的集合论出发](#set-theory)
- [2. 事实导向：把“什么成立”写进源码](#fact-oriented)
- [3. 自下而上：让已证明的事实推动后续证明](#bottom-up)
- [4. 每句话都留下什么：可检查知识记录](#execution-model)
- [5. 人类-AI-Litex 循环工作流构建](#interaction-loop)
- [6. Litex代码如何编译成Lean代码，并与Mathlib兼容](#compatibility)
  - [个人思考：Litex补齐了AI推理的范式缺口？](#summary-bottom-up-and-top-down)
- [7. 从语言到生态：Litex 想扮演什么角色](#ecosystem-role)
- [8. 追寻与众不同的艺术](#conclusions)
  - [特别感谢](#special-thanks)

<a id="overview"></a>

## 0. Litex 蓝图总览

AI 正在推动全人类进入“推理丰盈”的时代：答案和证明可以大规模生成，但大模型输出本身并不自动具备可信性、可解释性，也不必然促进人类理解。以数学为例，正如[陶哲轩在 2026 年 ICM 的公开讲演](https://www.youtube.com/watch?v=M0--ZH1lOzg)中所说，数学的未来需要从关注证明生成，转向证明的验证、阐释与消化。更普遍的问题是：如何将 AI 生成的推理转化为可检查、可理解、可复用的共同知识？这一问题不仅关乎数学，也关乎未来所有行业的知识生产。若能解决，人类才能更可靠地理解和利用 AI 的推理，形成真正有效的人机协同，并为新科学理论的产生创造条件。

*自然语言便于理解，却难以保证严格验证；形式化代码能够验证，却常常难以理解。Litex本身是这样的科学（数学问题），它想要实现的是连接自然语言和可信推理的形式化语言：它接近自然的数学表达，同时反馈清晰、结构化的验证流，使用户看懂每一步的作用及其数学依赖关系。*

*Litex是一门易学易用的形式化语言。它以集合论为基础，自下而上构建证明流，并把人类、AI 与验证器放进同一个闭环：人类给出数学意图，AI 提出或修复下一条事实，Litex 检查并返回依据或停止位置，由此循环积累可检查的数学知识。原理上，任何 Litex 代码都能编译成 Lean，并接入 Lean/Mathlib 生态，Litex到Lean的编译器预计2026年底完成。*

<details>
<summary><strong>站在 Lean 的肩膀上</strong></summary>

以 Lean 为代表的现代形式化语言，为 AI for Math 和“数学的工程化”奠定了不可替代的基础。然而，无论 AI 如何发展，能够熟练掌握 Lean、类型论及其工程体系的人，仍可能只是少数。Litex 并非试图取代 Lean，而是探索另一种形式化视角：让更多人能够直接书写、检查和理解严格的数学知识。

科学史反复表明，从全新的出发点重新审视已有问题，往往能够推动原有领域发展，甚至孕育新的学科。进入 AI 时代，复杂问题不断涌现，人们也越来越需要可信、可扩展且可解释的推理。在这一过程中，形式化方法将扮演越来越重要的角色。因此，多一种像 Litex 这样的探索，本身就是有价值的。

下面直接放三组来自[代表性 Lean–Litex 示例对照](Representative_Lean_Litex_Example_Comparisons.md)的代码。为保持表格简洁，Lean 示例省略了 `import` 行。它们比较的是默认接口，不是证明长短，也不声称两种语言的能力边界完全相同：

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

**Litex 不只是为形式化专家而创造的工具，它的目标更是让更多人成为形式化专家，让Math For AI成为可能。**

全文沿五个相连的问题展开：用户看见什么，源码保存什么，推理如何积累，证明过程如何呈现，结果如何独立复核。

1. **集合论对象**：用户直接看见集合、元素、函数和关系，而不必先管理抽象的承载类型。
2. **事实中心**：源码记录“什么成立”；检查器负责寻找依据，并检查相关对象和表达式是否良定义。
3. **自下而上积累**：每个通过验证的事实都会进入上下文，供后续推理使用；这是默认的推理方向。
4. **可追溯的证明流**：系统整理并输出从定义、前提到结论的前后依赖关系，使整个证明过程成为可阅读、可检查、可复用的结构化信息；出错时指出失败发生在哪里。
5. **Lean 复核**：已有覆盖路径可以翻译为 Lean 证明对象，并交由 Lean 内核独立检查；目前覆盖范围仍不完整。

全文通过比较 Litex 与 Lean 的写法，展示五项设计如何降低理解成本。如果您是Lean用户，可以先粗略地把Litex和Lean的默认流程理解成：

```text
Lean：命题 → 证明目标 → 证明指令与细化 → 证明对象 → 内核检查
Litex：对象和事实 → 内核检查并寻找依据 → 已验证事实扩展上下文
```

> **写给编程语言设计者：**
>
> Litex 的设计初衷其实非常简单：正如 Fortran 和 C 抽象了汇编语言，让系统工程与科学计算变得更容易；Python 又进一步抽象了 C 的部分使用场景，让没有专业编程背景的人也能参与其中。随着编程语言越来越易学、易用，越来越多人成为程序员，计算机行业也由此不断拓展。
>
> Litex 希望在数学推理与形式化验证之间建立类似的抽象层，让用户不必被底层实现细节牵绊，而能够把注意力真正放在思考本身。

> **写给数学背景以外的读者：**
> 
> 在数学之外，Litex希望用简单的语法表达对象、关系、条件与规则，再用清晰的验证反馈，邀请我们探索人类直觉、机器验证与数学知识之间的另一种表现形式。甚至在数学之外，Litex 还希望探索形式化语言在真实知识工作中的入口：从 AI 安全、AI输出可解释性、金融风控、精密软件工程，到物理化学、医疗、法律和工程。欢迎更多非数学专业背景的工作者使用Litex在自己的行业中用形式化工具，理解依据、发现冲突、预防错误。

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

Mizar、Isar、ACL2 和 Naproche 已支持前向文本、定理累积或逐步检查，因此“自下而上”并非 Litex 独有。Litex 检验的是组合：普通事实自动触发局部验证，通过后扩展上下文，同时让已接受或停下来的路径保持可见，供用户或人工智能检查和修复；只有常规验证不足时才写显式证明结构。更完整的比较见第 4 节的小结“Litex 与 Naproche——相近目标，不同核心接口”。

</details>

<a id="execution-model"></a>

## 4. 每句话都留下什么：可检查知识记录

我们读数学时，一句话从来不是孤零零地出现。写下一个事实的同时，我们也会在脑中浮现它所依赖的定义、前提和前面已经确认的事实；这些内容共同形成一个不断生长的上下文，后面的推理便在这片已经建立的基础上继续向前。

Litex 想做的，是把这条通常只存在于脑中的数学心流，逐句化成代码：源码写下要建立的对象和要验证的事实，已经定义好的概念和已经证明的事实留在上下文中，后续语句在它们之上继续生长。

*Litex最与众不同的点是，它的运行过程不是黑箱。任何语句是如何成立的，引入了什么概念，对整个证明上下文产生了什么作用，都会被输出出来*。正是因为Litex有这样的结构化输出，Litex才能很容易地编译到Lean（或任何什么形式化语言），并将整个数学证明中概念和概念、事实和事实之间的关系严格地呈现出来。它记录并输出了每句话为什么成立、使用了哪些依据、产生了哪些引申，以及哪些内容真正进入了后续的数学上下文。

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
  "ok": true,
  "statement_results": [
    {
      "outcome": "success",
      "result": {
        "kind": "LetObjStmt",
        "statement": "let a = 1",
        "common": {
          "infers": {
            "stores": [
              {
                "fact_id": "f1",
                "statement": "a = 1",
                "reason": "object definition",
                "inferred_facts": []
              }
            ],
            "rule_applications": []
          }
        }
      }
    },
    {
      "outcome": "success",
      "result": {
        "kind": "Fact",
        "statement": "a + 1 = 2",
        "evidence": {
          "kind": "Verified",
          "well_definedness": {
            "kind": "WellDefinedFactResult",
            "fact": "a + 1 = 2",
            "proof": {
              "kind": "AtomicFact",
              "statement": "a + 1 = 2",
              "arguments": [
                {
                  "argument_index": 0,
                  "object": "a + 1",
                  "result": {
                    "value": {
                      "kind": "Direct",
                      "object": "a + 1",
                      "intrinsic_result_set": "C",
                      "target_requirements": [
                        {
                          "role": {
                            "kind": "BuiltinArgumentMembership",
                            "argument_index": 0
                          },
                          "expected_proposition": "a $in C",
                          "verification": {
                            "value": {
                              "kind": "AtomicFact",
                              "statement": "a $in C",
                              "proof": {
                                "kind": "Reuse",
                                "source": {
                                  "value": {
                                    "kind": "AtomicFact",
                                    "statement": "a $in C",
                                    "proof": {
                                      "kind": "Transform",
                                      "rule": {
                                        "kind": "TransparentDefinitionReduction",
                                        "definitions": [
                                          {
                                            "symbol": "a",
                                            "definition_object": "1",
                                            "defining_equality": "a = 1"
                                          }
                                        ]
                                      },
                                      "source": {
                                        "kind": "AtomicFact",
                                        "statement": "1 $in C",
                                        "proof": {
                                          "kind": "BuiltinRule",
                                          "diagnostic_label": "number in C",
                                          "evidence": {
                                            "kind": "Typed",
                                            "rule_id": "numeric.closed_membership",
                                            "value": {
                                              "kind": "ClosedNumericMembership",
                                              "expected_target": "1 $in C",
                                              "target_set": "C",
                                              "evaluation": {
                                                "expression": "1",
                                                "value": "1",
                                                "step": {
                                                  "kind": "Literal",
                                                  "literal": "1"
                                                }
                                              }
                                            }
                                          },
                                          "subgoals": []
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      ]
                    }
                  }
                },
                {
                  "argument_index": 1,
                  "object": "2",
                  "result": {
                    "value": {
                      "kind": "Direct",
                      "object": "2"
                    }
                  }
                }
              ],
              "predicate": {
                "kind": "SuccessVerifyAtomicPredicateWellDefinedResult",
                "name": "=",
                "expected_arity": 2,
                "domain_checks": []
              }
            }
          },
          "proof": {
            "kind": "AtomicFact",
            "statement": "a + 1 = 2",
            "proof": {
              "kind": "Reuse",
              "source": {
                "value": {
                  "kind": "AtomicFact",
                  "statement": "a + 1 = 2",
                  "proof": {
                    "kind": "Transform",
                    "rule": {
                      "kind": "TransparentDefinitionReduction",
                      "definitions": [
                        {
                          "symbol": "a",
                          "definition_object": "1",
                          "defining_equality": "a = 1"
                        }
                      ]
                    },
                    "source": {
                      "kind": "AtomicFact",
                      "statement": "1 + 1 = 2",
                      "proof": {
                        "kind": "BuiltinRule",
                        "diagnostic_label": "calculation",
                        "evidence": {
                          "kind": "Typed",
                          "rule_id": "equality.rational_normalization",
                          "value": {
                            "kind": "RationalNormalization",
                            "expected_target": "1 + 1 = 2",
                            "left_evaluation": {
                              "expression": "1 + 1",
                              "value": "2",
                              "step": {
                                "kind": "Binary",
                                "operator": "Add",
                                "left": {
                                  "expression": "1",
                                  "value": "1",
                                  "step": {
                                    "kind": "Literal",
                                    "literal": "1"
                                  }
                                },
                                "right": {
                                  "expression": "1",
                                  "value": "1",
                                  "step": {
                                    "kind": "Literal",
                                    "literal": "1"
                                  }
                                }
                              }
                            },
                            "right_evaluation": {
                              "expression": "2",
                              "value": "2",
                              "step": {
                                "kind": "Literal",
                                "literal": "2"
                              }
                            }
                          }
                        },
                        "subgoals": []
                      }
                    }
                  }
                }
              }
            }
          }
        },
        "store": {
          "fact": "a + 1 = 2",
          "fact_id": "f2",
          "infers": {
            "stores": [],
            "rule_applications": []
          }
        }
      }
    }
  ]
}
```

</details>

这份记录把“这句话为什么能写下来”拆成了可追踪的局部步骤：先确认 `a + 1` 的参数满足运算所需的集合条件；再沿着已定义的 `a = 1` 透明化简为 `1 + 1 = 2`；最后由数值规范化规则完成计算。对读者来说，它至少回答了五个局部问题：

| 读者想知道什么 | 记录中看什么 |
| --- | --- |
| 语句和语句类型 | 语句内容与类型（`statement`、`kind`）：这是定义符号、定义谓词、定义函数，还是验证事实？ |
| 这句话是否有意义 | 良定义性检查（`well_definedness`）：对象和运算是否处在允许的定义域内？ |
| 为什么成立 | 证据和证明过程（`evidence`、`proof`）中的良定义性检查、定义化简与规则依据 |
| 它是否成为后续基础 | 保存结果（`store`）和已接受上下文 |
| 检查过程中得到什么引申 | 引申结果（`infers`）及其规则应用 |

例如，`let a = 1` 是定义符号 `a`，并记录 `a = 1`；`a + 1 = 2` 则是在当前上下文中验证一个事实。良定义性检查先确认语句是否有意义：例如 `1 / 0 = 1 / 0` 虽然两边形式相同，但 `0` 不能作为除法允许的分母，因此这个语句不满足良定义性要求。

<details>
<summary><strong>展开查看：Litex执行结果</strong></summary>

当我们输入 ` 1 = 0 ` 时，Litex的输出是

```json
{
  "error_type": "VerifyError",
  "result": "error",
  "line": 1,
  "message": "verification failed",
  "type": "equality fact",
  "statement": "1 = 0",
  "phases": {
    "verify_well_definedness": {
      "status": "success"
    },
    "verify_process": {
      "status": "error",
      "message": "verification failed"
    },
    "affect_environment": {
      "status": "not_run",
      "message": "previous phase failed"
    }
  },
  "previous_error": {
    "error_type": "UnknownError",
    "result": "error",
    "line": 1,
    "message": "unknown result",
    "type": "equality fact",
    "statement": "1 = 0",
    "failed_goal": "1 = 0",
    "unknown_result": {
      "type": "atomic fact unknown",
      "goal": "1 = 0"
    }
  }
}
```

这样的错误输出也是很宝贵的。当我们设计人类-AI-Litex交互流时，我们可以记录下来我们曾经犯过的错误，就能积累更多的数学形式化经验，让代码书写越来越高效和正确。

</details>

*Litex的核心就是这个简明、严谨、格式化的验证流输出。*从一条用户可以读懂并参与的执行路径出发，Litex 同时保留一份结构化知识记录。这份记录起到了4个作用：

1. **给人阅读**：把语句、依据和上下文变化做成交互式教科书。初学者不必再因为不知道某句话为什么成立而停在原地。
2. **给人工智能协作**：把每次成功、停止和失败的依据返回给人工智能，使它可以写 Litex、根据反馈自动纠错并逐步改进，形成“人—人工智能—Litex”的循环。
3. **给知识结构使用**：从定义、事实、引用和引申中生成定义与定理的依赖关系图，直观展示每个概念如何相互连接。
4. **给 Lean 复核**：根据记录中的定义、事实和验证依据设计 Litex 到 Lean 的编译器，把生成的等价 Lean 代码交给 Lean 内核复核，并接入 Lean 生态。

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
  → 在支持范围内交给 Litex 到 Lean 的编译器和 Lean
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

<!-- litex:skip-test -->
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
  "result": "rejected_rolled_back",
  "failed_phase": "verify_process",
  "verifier_evidence": "cannot prove then-clause; failed goal $converges_to(fn(n N) R {c * s(n)}, c * a)"
}
```

已接受上下文不变。记录说明：定义给出的是要证明的形状，不是现成结论；必须先为每个 `epsilon` 取出并交出合适的 `N0`。AI 只修这一片段：

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

## 6. Litex代码如何编译成Lean代码，并与Mathlib兼容

Litex 可独立工作，拥有语法、运行时和验证内核。如果你相信Litex内核是没有bug的，那它不编译成 Lean 也能为你检查良定义性与事实并提供反馈。

但在大型数学系统上，Lean有不可比拟的优势：Lean/Mathlib生态成熟、可复用的数学对象和定理库丰富、内核小而可审计。Litex希望能接入Lean的生态，如此Lean社区也能从Litex中受益，Litex可以在一些数学方向为Lean提供更易读、更易写的数学接口。

*同时，Litex到Lean的编译器还为 Litex 的严格性提供了保障。目前Litex的Rust 源码接近 20 万行，含数百条规则；其可信实现面远大于 Lean 的小内核，不可能像Lean内核那样真的经过检查。如果每一句Litex语句都能编译成对应的Lean代码，那么Litex的严格性就有保证了。*

> 目前Litex到Lean的编译器还处于实验阶段。从原理上，Litex的处理对象、验证机制，都是能对应到Lean/Mathlib的代码的（Litex基于集合论，Mathlib有集合论的包；Litex的每个验证机制，都能对应成Lean的若干个tactic的组合）。预计2026年底会完成这一工程。

<details>
<summary><strong>示例：Litex代码如何编译成Lean</strong></summary>

Litex编译成Lean，并接入Mathlib-Style的Lean代码，要经过以下过程：

`Litex 源码 → Litex 验证 → ToLean 编译 → Lean 内核复核 → 手写 adapter → Mathlib 定理`

> Litex编译成Lean的过程非常像C语言代码编译成汇编。我们知道汇编语言的代码之所以看起来像乱码是因为源码里写了很多内存地址。不管是新开地址和使用该地址时都要显式把地址写出来。Lean代码给每个事实都取了名字，在调用对应事实时也需要显式地把名字附上。Litex的内核在处理Litex代码时，替用户维护了这样一张事实表，同时在验证时会从该事实表中搜索到对应的事实来辅佐证明当前想要证明的东西。这个搜索过程的分叉多（Litex有几百条内置验证规则）而不深（每个验证规则都很直白，任何内置规则可以被编译成若干条Lean的tactic）。

举例：我们想要证明前`n`个正奇数之和是`n^2`。我们先写下Litex的源码：

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

Litex因此可以视作Lean的一个更可读的，更容易理解的前端语言。用户写下Litex代码，从Litex代码中理解整个证明过程，然后编译成Lean确保验证性并接入Mathlib生态。我相信这是非常值得探索的一个方向。

</details>

<a id="summary-bottom-up-and-top-down"></a>

<details>
<summary><strong>个人思考：Litex补齐了AI推理的范式缺口？</strong></summary>

在数学实践中，自下而上的证明流（从前提出发，积累更多事实），与自上而下的证明流（分解最终结论，直到最终和前提匹配上），构成了数学证明时的不同视角和思路。Litex的源码代表了前者的思维模式，Lean代码代表了后者。那么AI更偏好哪一种思维模式呢？

先看自下而上的证明流。大部分数学教材都是基于自下而上的行文模式写的，这也是人类更适应的思维范式（试想，我们不会从数学最后一页开始读书！）。大模型都是在互联网中的数学知识上进行训练的，因此AI更容易阅读Litex代码。同时，让AI Agent去写Litex代码时，让它和Litex的输出交互，了解每段证明为什么对，哪里出错，更容易形成`人类-AI-Litex`的证明流构建。

再看自上而下的证明流。大模型的训练围绕着目标函数和奖励信号展开。因而，AI 未必天然具备稳定的、从第一性原理自下而上展开的推理能力；在许多任务中，它更容易从期望结果或评价信号反向组织一条看起来能够到达结果的路径。

因此，两种思维模式都很宝贵：自下而上适合积累可复用的局部事实、暴露中间依据；自上而下适合澄清目标、选择方向、压缩搜索空间。Litex 与 Lean 的连接，正可以把这两种方向放进同一条可检查的证据链，并让人类和 AI 在各自擅长的方向上协作。

</details>

<a id="ecosystem-role"></a>

## 7. 从语言到生态：Litex 想扮演什么角色

所有的设计合在一起，使 Litex 希望成为人和 AI 共同生产、使用可检查推理的基础设施。

**Litex 面向人类与 AI：既是可读推理前端，也是可信推理数据生产层，并尝试通过 Lean/Mathlib 接入现有生态。** 它希望也服务于 AI、工程师和其他领域实践者。

未来的数学家工作流，一定会是AI+人类协同工作，做出证明，然后把证明生成对应的形式化代码确保其正确性。这里生成的形式化代码可以是Lean，可以是Litex。Litex希望成为Lean的更可读的前端语言，降低形式化代码的阅读和书写门槛。

前面的几节说明了，这个角色并不是若干功能的简单相加。集合论对象、事实导向源码、自下而上生长的已验证上下文、极简语法、贴近自然数学的表达，以及结构化验证结果，共同进入了同一套协议，使数学本身和数学的构造证据都能够被保存。

| 生态角色 | Litex 希望产生的实际成果 |
| --- | --- |
| 可读推理的前端 | 人可以直接审核的数学对象、条件、中间事实和结论 |
| 可信推理数据的生产层 | 经过机器检查的事实与验证来源、明确的停止边界，以及被显式标出的可信边界 |
| 现有生态的接入层 | 当前已支持源码路径对应的 Lean 证明对象，以及明确分离、由 AI 或人类编写的新增 Lean/Mathlib adapter |

当然，Litex现阶段更像是处于 `proof of an idea` 的阶段。即便它本身已经有几十万行代码，它在行业上下游中的探索仍然稀缺。这也是Litex下一阶段会着重关注的：如何让从0到1的原始创新，成为从1到10的早期价值兑现。对Litex感兴趣的朋友可以联系 litexlang@outlook.com 。

<details>
<summary><strong>Litex的生态位</strong></summary>

编程语言很少凭空流行。它们通常诞生于新的技术能力与新的社会需求交汇之处：Fortran 伴随大型机计算能力和高性能计算需求出现，C 与 Unix 的系统编程需求彼此塑造，JavaScript 与 Java 随互联网时代的前端和后端开发普及，Python 和 CUDA 则分别回应了 AI 框架快速迭代与底层高性能计算的需要。Lean 的新一轮发展，也与 AI for Math 对可靠形式化的需求高度重合。

Litex 想寻找的，正是下一个由 AI 时代催生、目前还难以准确命名的场景。AI 将持续生成大量候选推理，新的知识工作也会因此需要更低成本的检查、解释、组织和复用。我相信这样的场景应该会很快出现。

</details>

<a id="conclusions"></a>

## 8. 追寻与众不同的艺术

<!-- 这一段比较理想主义一点。因为AI时代大家过度关注实用主义了，容易忽略一个原生的、创新的、与众不同的新解决方案带来的长期的影响力。不管是数学界，还是任何科学，大家都鼓励对同一问题的不同角度、不同解决方案的出现。这样的不同的观点，往往才是科学史上真正突破的来源，最终可能会带来更大的效益提高。 -->

在星光熠熠的科学史上，对同一问题的全新视角、全新解答，往往极大推导了原来领域的发展，甚至催生了全新的学科。在效率至上的AI时代，即使在数学这么以长期主义著称的学科，我们仍然很容易迷失在抢先发布、刷榜宣传的局部最优解中，而忽略了对第一性原理的重新思考和原始创新。

这并不意味着要否定已经取得巨大成功的 Lean。Lean 以优雅的类型论、可靠的内核和丰富的 Mathlib 生态，证明了数学能够被严谨地工程化。Litex 更想追问的是：在保持可编译到 Lean、接受内核复核的前提下，形式化语言能否采用另一种更贴近自然数学的接口，让源码、验证过程和数学依赖关系都更容易被人理解、书写和参与？这不是寻找一个替代 Lean 的答案，而是为形式化语言增加一个值得验证的方向。

当然，Litex 也许不会成为唯一的道路，而且它不需要成为唯一的道路。Litex希望世界会因为数学而更好，数学世界会因为形式化语言而更好。我认为在Lean之外，有Litex这样的“非标准解法”是有长期价值的。

<a id="special-thanks"></a>

### 特别感谢

Litex 由沈嘉辰与 Litex 团队创建和维护。特别感谢 Wei Lin、Siqi Sun、
Peng Sun、Yi Wang、Chenxuan Huang、Yan Lu、Sheng Xu、Keyao Zhu、Xingjian Ma
和 Zhaoxuan Hong 对项目给予的支持与建议。

### 相关链接

1. 如果想直接试用例子，并查看 Litex 生成的输出和知识图谱，可以访问 [litexlang.com](https://litexlang.com)。

2. 如果关注内核实现，可以查看 [golitex 仓库](https://github.com/litexlang/golitex)。

注：当前仓库同时保留已检查成果、实验和未完成工作。*公开可见不等于宣称完成*；能力应以测试、带日期的状态、可信边界和已知限制为准。
