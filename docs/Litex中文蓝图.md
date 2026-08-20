# Litex：让数学自我验证的形式化语言

文档由沈嘉辰创建和维护。

官网页面: https://litexlang.com/doc/Litex中文蓝图

英文版: https://litexlang.com/doc/Litex_Blueprint

> **Litex 是一个实验性爱好项目，仍处于 beta 阶段。请预期会有边缘问题。**

## 目录

- [Litex 蓝图总览](#overview)
- [背景：AI 时代需要形式化语言](#background)
- [1. 基于集合论：让集合论知识保持集合论的样子](#set-theory)
  - [从群的两种定义模式，看如何从头搭建一个数学理论](#group-comparison)
- [2. 事实导向：从日常数学的工作流出发——定义、定理和证明](#fact-oriented)
- [3. 自下而上构建证明流](#bottom-up)
  - [同一证明的两种推进方向：自上而下与自下而上](#two-directions)
- [4. 和 Lean 兼容：通向 Lean 可信生态](#compatibility)
- [总结](#conclusions)
- [附录：Litex 为满足成功条件正在做什么](#appendix-conditions)

<a id="overview"></a>

## Litex蓝图总览

*Litex 是基于集合论的，事实导向的，自下而上构建证明流的，和Lean兼容的，形式化语言。*

1. 基于集合论：Litex 以 ZFC 集合论为基础，让数学对象统一通过集合和成员关系来组织；同一个对象可以属于多个集合；对象、事实、数学语句是分离的。作为对比，Lean 的集合 `Set α` 则先依赖更抽象的载体类型 `α : Type*`，数学对象、数学事实都是某种类型。类型论提供更强的泛化与组合能力；Litex 的取舍，是针对集合论及其上的常见数学知识提供更直接的表面接口。
2. 事实导向：Litex 源码主要写“什么数学事实应当成立”，内核根据事实的谓词和参数，从内置规则、已证明事实和等式匹配中寻找验证方式。对象与表达式的良定义性，也会在事实被接受前自动检查。作为对比，典型的 Lean tactic 源码主要写“下一步怎样处理 Goal”，Infoview 则显示操作之后还剩什么 Goal。
3. 自下而上构建证明流：数学证明既可以从已知条件出发，不断得到新事实并最终汇聚到结论；也可以从最终 Goal 出发，把它反向化约成已知条件。Litex 默认采用前一种、让上下文随已验证事实向前生长的工作流；Lean 常见的 tactic 交互通常采用后一种。两者都不把另一种方向排除在表达能力之外。
4. 和 Lean 兼容：Litex-to-Lean 编译器的目标，是把内核已经找到的验证路径翻译成 Lean proof term，再由 Lean kernel 独立检查。当前编译器只覆盖部分验证路径；“所有 Litex 源码都能编译成 Lean”是尚未完成的方向，不是 beta 版本已经达成的能力。

理想状态是，用户在使用 Litex 时，能够保持与进行非形式化数学时相同的心流：把注意力放在数学对象、条件、中间事实和结论上，而不必先面对抽象的数学理论、陌生的形式化语法或庞大的外部库。Litex 则像一位 copilot，在一旁提供快速、局部而可追踪的验证反馈。*希望 Litex 能让更多各行各业的非专业人士更容易进入形式化数学的世界。*

我会在后文先交代背景，然后依次回答这句总纲中的四个关键词：**基于集合论、事实导向、自下而上构建证明流、和 Lean 兼容**。希望这个高度凝练、主观判断、思维发散的蓝图能让读者对 Litex 的设计理念和目标有一个整体印象，跟着Litex作者的思路"重新发明一遍 Litex"。

<a id="background"></a>

## 背景：AI 时代需要形式化语言

从阿拉伯数字，到莱布尼茨的微积分符号，再到 TeX 和 LaTeX，数学史上重要的新符号体系往往不只是缩短书写；它们还会潜移默化地改变人们看见问题、组织推理和探索新方向的方式。形式化语言是数学符号体系的一个新阶段：它不仅让人类能用更精确的方式书写数学，也让机器能严格检查这些书写。今天，AI 正在让数学证明候选的生成变得更广泛、更规模化。当证明不再只是少数人手工写下的文本，关键瓶颈也会从“能否生成一段看起来合理的论证”，逐渐转向“能否可靠地检查、复用和积累它“。

*然而主流的形式化语言和证明助手，仍然主要面向专业研究者。它们的语法、交互和工作流往往与日常数学书写有较大差异，初学者需要花费相当时间熟悉这些差异，才能用它们表达自己想要的数学。在数学以外，AI安全研究者、软件工程师、物理学家、经济学家、统计学家等，也都可能需要用形式化语言表达数学，但他们不一定有时间或兴趣去学习深奥的证明助手的内部机制。*

Litex 想做的，就是让这层技术走近寻常学习者和数学使用者。它追求的理想是：**想表达什么数学，就能用形式化语言表达什么。**例如，一个已经掌握中学数学的人，应当能在很短时间内学会用 Litex 表达相应的中学数学，而不必先成为证明助手专家。

要理解这个目标为何需要不同的语言设计，可以先看形式化证明与日常数学常见工作流之间的关系。

> **说明** 下文仍以 Lean 为贯穿全文的主对照，因为它能最具体地
> 显示 Goal-first 与 fact-first 的差异。文中对 Mizar、Isabelle/Isar、Rocq、
> ACL2 和 Naproche 的引用，用于说明 Litex 在现有设计空间中的位置：Litex 是独立设计的，
> 并非从这些系统派生而来。引用它们是为了说明邻近思路和最终形成的差异，
> 不表示直接的思想影响关系。

<details>
<summary><strong>阅读前的基本术语：形式化语言、Goal、tactic 与 kernel</strong></summary>

*如果你没有使用过 Lean 或其他证明助手，可以先读这一小节；跳过它也不影响后面的数学例子。*

- **形式化语言（formal language）**：语法和含义由明确规则规定、因而可以被机器解析和检查的语言。“形式化”说的是表达规则具有精确含义，不是行文显得正式；形式化语言也不一定是通用编程语言。
- **证明助手（proof assistant）**：帮助用户表达证明、给出交互反馈，并由机器检查证明的软件。Lean 是一个具有通用编程能力的证明助手。
- **Goal（证明目标）与 Infoview**：Goal 是当前等待证明的命题；Infoview 是 Lean 编辑器中显示当前 Goal、局部变量和已知假设的窗口。
- **上下文（context）**：当前作用域内可使用的变量、定义、假设和已验证事实。加入一条新事实会扩展上下文，让后面的推理可以使用它。
- **tactic（证明指令）**：操作当前 Goal 的命令，例如引入变量、按等式改写或把一个目标拆成若干子目标。tactic 描述“下一步怎样证明”，本身不是最终接受的证明对象。
- **proof term（证明对象）与 elaboration（细化）**：proof term 是机器可以检查的完整证明对象；elaboration 是系统补全源码中省略的信息，并把用户代码变成完整 proof term 的过程。
- **kernel（内核）**：在 Lean 中，kernel 是按照基础规则核验 proof term 的可信核心。tactic 可以很复杂，但其结果仍须通过 kernel 检查；kernel 通常不负责替用户选择高层证明步骤。
- **内核/ verifier（检查器）**：对“负责检查”的程序部分的宽泛称呼。Litex内核不仅核验对象是否良好定义，还会从内置规则和当前上下文中寻找事实的验证依据，因此它不能直接等同于 Lean 的 kernel；本文后面所说的 Litex 可信边界——也就是系统正确性所依赖、必须信任的部分——也相应更大。

可以先把两种流程简化成：

```text
Lean：命题 → Goal → tactic 与 elaboration → proof term → kernel 检查
Litex：对象和事实 →内核检查并寻找依据 → 已验证事实扩展上下文
```

</details>

<a id="set-theory"></a>
<a id="goal-2"></a>

## 1. 基于集合论：让集合论知识保持集合论的样子

Litex 直接以集合、成员关系和集合之间的关系组织它的表面语言。因此，当问题本身就是集合论问题时，用户可以直接写集合、子集和交集，不需要先引入一层承载这些集合的类型。

下面这段 Litex 代码声明了交集关于子集关系的单调性：

```litex
forall s, t, u set:
    s $subset t
    =>:
        intersect(s, u) $subset intersect(t, u)
```

这不是一个留待补全的证明空洞，而是交给内核检查的完整事实。这个事实的日常数学读法就是：取 `intersect(s, u)` 的任意成员 `x`，`x` 同时属于 `s` 和 `u`；由 `s $subset t` 可知 `x` 也属于 `t`，因而属于 `intersect(t, u)`。用户声明应当得到的数学结果，内核负责从交集成员的展开、成员关系沿子集的传递，以及右侧交集成员的重新组合中寻找验证路径。

下面是 Lean 版本的同一命题。示例出自 Lean 经典教科书《Mathematics in Lean》的集合论章节。

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

这段 Lean 代码的第一层对象不是集合，而是 `α : Type*`：`s`、`t`、`u` 随后才被声明为这个载体类型上的 `Set α`。更准确地说，Lean 中的 `Set α` 是以 `α` 为定义域的谓词；`Type*` 及其 universe 层级则提供比集合更抽象、更通用的类型论组织方式。这种设计让同一套定理可以在任意载体类型上复用，也是 Lean 表达力与可组合性的重要来源。

Litex 选择了另一种任务边界。因为它直接以集合论对象和成员关系作为基础表面，语言与内核可以针对集合、成员、子集、交集和并集等高频集合论知识提供专门的语法与验证路径。在这个任务上，用户只需声明三个 `set` 和预期的包含关系，代码因而更接近日常集合论书写，也明显更简洁。

这里的差异不应简化成“短代码一定比长代码强”。Lean 也可以用更短的 proof term 或自动化证明同一命题；上面的版本刻意保留《Mathematics in Lean》中展开定义、拆开交集成员再重新组合的教学路径。真正的对比是默认接口：Lean 先给集合一个类型论载体，再由用户或 tactic 构造证明；Litex 则把常见集合论关系直接做成语言可以识别和检查的数学事实。

这种集合论式表面并不表示 Litex 没有约束。函数参数的定义域、返回集合、结构字段和集合成员关系仍然需要通过良定义性检查；只是这些约束尽量写在数学家本来就会写的位置。Litex 也保留 `template` 等参数化构造，因为普通数学确实需要按载体、参数或假设索引的对象族；Litex 并不把自己描述成完整的依赖类型论。

同样的选择也会延伸到群这样的数学结构：结构仍然必须有载体，运算仍然必须说明输入和输出落在哪里，区别在于这些约束首先以类型和函数呈现，还是首先以集合、成员和集合上的运算呈现。

> **设计空间中的位置。** 集合论式的表述并非 Litex 首创：
> [Mizar 的数学库](https://wiki.mizar.org/library/) 基于 Tarski–Grothendieck 集合论；
> [Lean](https://lean-lang.org/doc/reference/latest/The-Type-System/) 和
> [Rocq](https://rocq-prover.org/doc/V9.2.0/refman/language/core/index.html) 向用户展示依赖类型论内核；
> [Isabelle/HOL](https://isabelle.in.tum.de/website-Isabelle2024/dist/library/Doc/Isar_Ref/HOL_Specific.html)
> 使用多态高阶逻辑。Litex 的问题更具体地落在面向用户的对象接口上：
> 一套小型、以成员关系为中心的集合论式表层，能否在不要求用户先管理类型
> universe 的前提下，覆盖有实质内容的数学？

<a id="group-comparison"></a>

### 从群的两种定义模式，看如何从头搭建一个数学理论

Litex 选择集合论，一个重要意义不只是让集合、成员关系和函数保持日常数学的样子，也在于为不同数学理论提供一套小而统一的共同起点。集合、函数、关系和运算本来就是数学书组织分析、抽象代数和线性代数的常用语言；从它们出发，一个领域的定义和定理可以主要沿着自身的数学依赖逐层生长，而不必先服从某个大型外部库对该领域的既有编码。这里把这种能力称为**数学理论的自举**，或者**自包含的理论构建**。

外部库可以提供可复用的成果、缩短建设过程，却不应决定哪些数学能够被表达和推演。下面的群足够小，可以把这种取舍展示清楚：两个片段表达同一种熟悉的数学结构和同一个单位元唯一性结论，但对“载体是什么”“二元运算是什么”以及“结构规律如何进入后续证明”给出了不同的默认接口。

#### Lean：`Type` 上的 record 与柯里化函数

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

这段 Lean record 首先要求 `Carrier : Type`：群的元素、运算和规律都依赖这个载体类型。二元运算 `Carrier → Carrier → Carrier` 按函数类型的结合方式表示 `Carrier → (Carrier → Carrier)`；结构规律则成为 `mul_assoc`、`one_mul` 等可投影的具名字段。这套函数式、类型论式接口具有很强的抽象与组合能力，也便于大型库精确复用；与此同时，作者需要接触宿主语言的函数构造和库的命名接口，并知道当前需要哪个定理变体与等式方向。上面的唯一性证明就显式写出了 `G.one_mul`。

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

Litex 从 `s nonempty_set` 开始，把群直接建模为非空集合 `s` 上的结构。`mul fn(x, y s) s` 直接表示一个接收 `s` 中两个元素、返回 `s` 中元素的二元运算；结构规律则以普通数学事实写在 `<=>:` 中。用户可以从集合、运算、单位元、逆元和规律这些数学材料出发，亲手看着“群”逐层建立起来。单位元唯一性也直接写成 `identity = G.mul(G.one, identity) = G.one`，由内核寻找相应的单位律实例和等式方向。Litex 并不禁止命名；值得长期引用的定理和公共接口仍然可以写成具名 `thm`，但普通结构规律和局部事实不必为了被使用而逐条进入一套需要作者记忆的命名接口。

这段 Lean 代码本身也说明，Lean 当然可以不依赖 Mathlib 的既有群接口而自行定义群；真正的区别不是“能不能”，而是哪一种体验被设计成默认路径。对 Litex 追求的写作体验而言，集合论尤其合适，因为集合、成员关系、函数和关系构成了一套跨领域而又接近日常数学的共同语言。Litex 仍然依赖自己的内核、内置规则和标准库；这里所说的“从头搭建”，是让分析、抽象代数或线性代数的源码依赖主要反映理论本身的数学结构，让外部库成为可选的加速器，而不是表达能力的边界。

这个例子也自然引出下一节：如果用户不必先说“我要调用 `one_mul`”，而可以直接写“这里应当等于什么”，那么源码的中心就不再是定理名和证明指令，而是数学事实本身。

<a id="fact-oriented"></a>
<a id="workflow"></a>

## 2. 事实导向：从日常数学的工作流出发——定义、定理和证明

这一节用定义、定理和证明说明“事实导向”具体改变了什么：用户源码主要保存数学上应当成立的对象和事实，内核则负责寻找、检查并解释它们的局部依据。

Lean 是一种常用的证明助手和形式化语言，能够严格检查人类和 AI 写出的形式化证明。它的默认交互以最终 Goal（当前待证命题）为起点：用户通过 tactic（证明指令）持续改写、分解或关闭当前 Goal，系统据此构造 proof term（证明对象），再交给 kernel（内核）检查。

> **Lean tactic：定理先给出最终 Goal → 用户声明应当如何改写、分解或关闭它 → Infoview 显示还剩哪些 Goal → tactic 构造 proof term → kernel 检查该 term。**

下面以这样一个例子开始：先定义序列收敛，再根据该定义证明——如果序列 `{s(n)}` 收敛到实数 `a`，那么序列 `{c * s(n)}` 收敛到实数 `c * a`。

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

上面的 Lean 证明展示了一种高度通用、抽象且可组合的模式，这种模式是 Lean 强大表达能力的重要来源。不过，它的默认推进方向与日常数学书写并不完全相同；初学者还需要熟悉相当数量的 tactic 关键词。相比之下，日常数学书写更常按下面的顺序推进：

1. 写下对象、定义和条件；
2. 看到一个熟悉的模式；
3. 使用已经知道的事实、定义或计算，写出下一条事实；
4. 让这条事实成为后续推理的上下文。

Litex 把这种日常数学工作流变成它默认的运行逻辑。整个过程可以概括为：

> **Litex：用户声明“什么应当成立” → 检查器寻找证明依据 → 输出解释该陈述为何以及如何通过验证 → 已验证事实扩展当前上下文 → 证明自下而上生长。**

仍以这个序列问题为例。对于初学者，下面的 Litex 代码读起来更接近日常数学表达：

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

<a id="goal-1"></a>
### 为什么普通 fact 不需要名字，也不需要 tactic？

收敛例子里，`abs(c) + 1 > 0`、`epsilon / (abs(c) + 1) $in R+` 和一连串不等式都没有名字。用户也没有逐行写“调用哪个 tactic、使用哪个库定理、朝哪个方向改写”；用户直接写下自己要得到的数学事实，内核再寻找能够验证它的规则和上下文依据。

> **事实导向最核心的人机分工是：用户写“我要证明什么”，Litex 寻找“这条事实可以怎样被验证”。**

**Litex 用户主要声明 *what*：“什么应当成立”；Lean tactic 用户主要声明 *how*：“应当怎样处理当前 Goal”。** Litex内核寻找能与结果匹配的证明依据，并解释找到的验证路径。Lean 的 elaboration（细化）过程按照用户的 tactic 指令构造对应的 proof term，Infoview（目标窗口）显示变化后的 Goal，kernel 检查该 term。

类比搭乐高的说明书：说明书会把每一步要做什么动作和做完这个步骤后得到的结果的图片给出来。Lean相当于源码里写的全是要做什么动作。Litex相当于源码里写的全是要得到什么结果，说明书里不写动作，动作由内核找。

注：这并不表示 Litex 禁止命名。经典定理、标准库接口或作者希望显式展示依赖时，仍然可写成用Litex的具名 `thm` 并用 `by thm` 调用。

下面展示Litex是如何在不需要名字和 tactic 的情况下，验证用户提交的事实。一言蔽之就是，一个事实要么由全称事实（内置或用户提供）验证，要么由已知具体事实和等式信息验证。内核会根据事实的谓词和参数形状，寻找可接受的验证路径。（当然Litex还提供了复杂的多的优化和策略，但它们不影响这个核心分工。）

<details>
<summary><strong>展开：内核如何按事实形状寻找验证路径</strong></summary>

#### 1. 用内置规则 匹配事实形状

一条 atomic fact（原子事实）可以直观地拆成“谓词 + 参数”。如果借用自然语言的比喻，谓词像动词，参数像这个判断所谈论的名词。例如：

```text
a + b >= 0
```

它的关系谓词是 `>=`，两个参数是 `a + b` 和 `0`；参数内部还带有可继续观察的结构：左侧是两个对象的加法，右侧是零。内核不需要先知道这条事实叫什么名字，就可以根据这个事实形状缩小候选范围。

先看本节的主例子：

```litex
have a R = 1
have b R = 2

a + b >= 0
```

在这个局部上下文中，用户提交的目标就是最后一行 `a + b >= 0`。内核看到谓词 `>=`，再看到左参数的外层形状是加法、右参数是 `0`，于是尝试相应的非负性内置规则。Litex内置了下面的这个规则：

```text
forall x, y R:
    x >= 0
    y >= 0
    =>:
        x + y >= 0
```

目标结论与内置规则的结论匹配后得到 `x := a`、`y := b`；内核再回头检查实例化后的前提 `a $in R`, `a >= 0` (1 >= 0)、`b $in R`, `b >= 0` (2 >= 0)，因而接受目标事实。

#### 2. 用用户提供的全称事实匹配

候选来源不只可以是内置规则。用户已经证明或明确假设的普通 `forall` 事实，也可以进入自动匹配：

```litex
abstract_prop p(x)

trust forall a R:
    $p(a)

$p(1)
```

面对目标 `$p(1)`，内核先按谓词 `p` 找到结论形如 `$p(a)` 的全称事实，再把参数 `a` 匹配为 `1`。这次实例化还要求 `1 $in R`；该条件能够通过检查，所以内核可以用这个全称事实验证 `$p(1)`。

注：abstract_prop 是 Litex 的一个语法糖，表示“声明一个抽象谓词，但不提供定义”。trust是Litex中的会产生warning的声明，表示这个事实不加验证地被认为成立。请谨慎使用trust，它通常只在测试或隔离示例中使用。

#### 3. 用 concrete fact 和已知等式匹配

第三类常见来源不是全称 规则，而是已经存在的 concrete fact（具体事实）：

```litex
abstract_prop q(x)

forall a R:
    $q(a)
    a = 1
    =>:
        $q(1)
```

验证 `$q(1)` 时，内核找到同谓词的已知事实 `$q(a)`。两个参数虽然不是同一段文本，但上下文还知道 `a = 1`，所以它们在当前等式信息下能够匹配；`$q(a)` 因而可以被运输为 `$q(1)`。

</details>

#### 总结：Litex源代码风格是，把”证明什么“写在源码里，把”怎么证明“交给内核找。

这样的书写风格也和日常数学书写更接近：数学家通常不会在每条推理中显式写出“我将使用哪条定理、哪个等式、哪个定义”，而是直接写下“我想得到的结论”，读者再根据上下文和已知事实理解它为什么成立。

> 有趣的是，编程语言通常分为函数式编程（JavaScript, Lisp, Lean等）和过程式编程(C/C++, Go, Rust等)两类。函数式编程通常更声明式，即源码更像是是告诉我们”要做什么“；过程式编程通常更命令式，即源码更像是告诉我们”怎么做“。Litex的风格更接近声明式编程：用户声明”要证明什么“，内核负责寻找”怎么证明“；而虽然Lean是函数式编程，但在写数学的时候更像是过程式编程：源代码负责告诉内核”怎么证明“。（个人观点）

> **设计空间中的位置。** 寻找局部证明依据并非 Litex 独有：
> [Lean `grind`](https://lean-lang.org/doc/reference/latest/The--grind--tactic/)、
> [Rocq `auto`](https://rocq-prover.org/doc/master/refman/proofs/automatic-tactics/auto.html)
> 和 [Isabelle/Isar](https://isabelle.in.tum.de/doc/isar-ref.pdf) 通过显式 tactic 或
> proof method 提供局部自动化；[Mizar](https://mizar.uwb.edu.pl/project/mizman.pdf)
> 有 empty justification；
> [ACL2](https://acl2.org/doc/index-seo.php?xkey=ACL2____DEFTHM) 可以在没有 hints 时
> 尝试证明 theorem event；[Naproche](https://naproche.github.io/) 则用自动定理证明器
> 检查受控自然语言中的证明步骤。Litex 更具体的假设是：能否让有界的、
> 由事实触发的 local justification 成为普通数学陈述的默认语义，并在成功后
> 把事实写回上下文、显示它的验证来源。

<a id="goal-3"></a>

## 3. 自下而上构建证明流

事实导向回答的是“一行 Litex 源码是什么”：它是一条等待内核验证的数学事实。自下而上则回答“这些事实如何组成证明”：每条已经验证的事实都会扩展上下文，让后续事实从已有结果继续生长。

Litex 的证明过程是自下而上的。它默认的推理单位是当前上下文中的下一条数学事实，而不是一个每行都必须立即推进的活跃 Goal。只要一条陈述位于当前作用域中、定义良好，并且能由现有上下文充分支持，内核就可以接受它、保存它、应用当前适用的推理规则，并把增强后的上下文交给后续陈述。几条数学分支也可以先分别生长，再由之后的陈述让它们汇合。

Lean 通常的交互式定理证明是 goal-directed（以目标为中心）的，典型方向是向后、自上而下。最终定理先确定最终目标是什么；局部 term（证明项）和 tactic 指令再在这个预期之下进行 elaboration，逐步把待完成的 Goal 分解或反推为更简单的子目标，直到 Lean 能组装出完整的 proof term。

两者的默认问题可以概括为：Lean 问“怎么去化简当前的目标，让目标能化约成已知条件”；Litex 问“根据已知条件，下一条能够推出的事实是什么？”

> 可以把写证明想象成搭乐高：一开始，我们拿到一批可用积木，也知道最终成品应当是什么。Lean tactic 的典型做法像从成品开始反向拆解，直到拆出的要求能够由手上的积木满足；Litex 的典型做法像从已有积木开始向前拼接，让一个个已经确认的局部结果最终汇聚成目标成品。这个比喻只说明默认推进方向，不表示 Litex 的验证标准更宽松，也不表示两种系统只能朝一个方向工作。

#### 例一：代数重写

这个局部重写例子展示同一条等式怎样沿两个方向展开。在 Lean 中，用户从待证明的 Goal 出发，用每条 `rw` 指定接下来调用哪个事实、按哪个方向匹配和替换：

```lean
-- Using facts from the local context.
example (a b c d g f : ℝ) (h : a * b = c * d) (h' : g = f) :
    a * (b * g) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]
```

对应的 Litex 写法把 Lean 从 Goal 出发执行的四次重写，反过来写成一条等式链。这条等式链从 Goal 的右端 `c * (d * f)` 出发，依次写出中间结果，最后到达 Goal 的左端 `a * (b * g)`：

```litex
claim:
    ?forall a, b, c, d, g, f R:
        a * b = c * d
        g = f
        =>:
            a * (b * g) = c * (d * f)
    c * (d * f) = (c * d) * f = (a * b) * f = a * (b * f) = a * (b * g)
```

1. 第一个等号对应 `rw [mul_assoc]`。
2. 第二个等号对应 `rw [h]`。
3. 第三个等号对应 `rw [← mul_assoc]`。
4. 第四个等号对应 `rw [h']`。

这四个等号与 Lean 的四条 `rw` 恰好逆序对应。Lean 的代码告诉系统“下一步调用哪个事实、朝哪个方向改写 Goal”；Litex 的代码则告诉系统“如果这些推理能够完成，关键的中间结果应当是什么”。内核再从当前上下文、等式匹配和结构规则中寻找每个相邻等式的依据。

#### 例二：集合包含

上面的例子涉及代数重写。为了说明上述交互方向的差异并不依赖计算，再看一个让成员关系沿集合包含关系传递的例子。Lean 从目标 `x ∈ c` 出发，通过 `apply` 逐步声明应当怎样证明它：

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

Litex 则直接声明应当建立的中间结果和最终结果，内核再从当前上下文中寻找它们的依据：

```litex
forall A, B, c set, x A:
    A $subset B
    B $subset c
    =>:
        x $in B
        x $in c
```

Lean有强大的infoview功能，让用户看到每次 tactic 执行后剩下的 Goal。

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

Litex 则在 runner trace 中显示的是每条结论为什么成立：

```text
"conclusions": [
  {
    "statement": "x $in B",
    "why_verified": {
      "type": "内置规则",
      "rule": "membership through a known direct set inclusion"
    }
  },
  {
    "statement": "x $in c",
    "why_verified": {
      "type": "内置规则",
      "rule": "membership through a known direct set inclusion"
    }
  }
]
```

除了自下而上和自上而下的工作流范式上的不同，从内核的输出上，又一次可以看到Litex和Lean的根本性差异：Litex源码里写的是what to verify，内核做的工作是how to verify；Lean源码里写的是how to verify，内核做的工作是确定what to verify。

> **说得尖锐一点：Lean 常见的 tactic 工作流，就像强制要求你读一本数学书时从最后一页开始读，写一篇论文时从最后一页开始写——先固定最终 Goal，再向后反推前面必须补出什么。**

> **同样尖锐地说：从第一性原理看，Litex 当前最大的问题，是它的可信内核太大。Litex 把数百条常见证明模式放进 builtin 和 infer rules，把工作从用户的 proof script 移进了可信计算基。证明工作并没有消失，只是被系统吸收了。要让 Litex 的验证结果再由可信边界更小且相对独立的 Lean kernel 复核，Litex 还需要把记录的验证路径编译成 Lean proof term；这一编译覆盖是可行的，但需要时间打磨。**

> **设计空间中的位置。** Mizar 和 Isar 已经支持向前展开的声明式证明文本，ACL2 会累积
> 可复用的定理数据库，Naproche 会逐步检查数学陈述。因此，“自下而上生长”本身并不是
> Litex 的差异化主张。Litex 真正检验的是这样一套组合：普通 fact 是能够扩展上下文的
> 可执行单元；local justification 不需要另行调用 proof method 就会启动；只有当
> 常规重建到达边界时，显式证明结构才出现。

<a id="compatibility"></a>

## 4. 和 Lean 兼容：通向 Lean 可信生态的简洁数学前端语言

Litex 首先是一门可以独立工作的形式化语言。它拥有自己的语法、运行时和内核一份 Litex 数学文档即使不编译成 Lean，也能直接接受 Litex 的良定义性检查、事实验证和局部证明反馈。因此，这里的“Lean 数学前端语言”说的是：Litex-to-Lean 编译器会把当前已经支持的验证路径翻译成 Lean proof term，并以逐步扩大覆盖面的方式连接 Lean 生态。*我期望Litex 的发展可以为 Lean 社区提供新的形式化数学内容和接口经验，Lean 的内核与 Mathlib 生态也能反过来帮助 Litex。两者的关系不是竞争，而是互补。*

Litex 的目标一开始就是成为一门为数学特化的语言；它的语法和交互契约更接近数学本身，而不是通用编程语言的抽象。使用 Litex 时，用户可以把注意力放在数学对象、条件、中间事实和结论上，并从内核获得快速、局部而可追踪的验证反馈。这对 AI 同样重要：生成系统可以围绕“下一条应当成立的数学事实”进行小步建议，再根据内核返回的具体依据或失败边界继续修正，而不必一开始就把数学意图完全降解为 elaboration、类型类、命名空间和 tactic 调用的细节。当然这些机制是 Lean 表达力与可组合性的重要来源，也是 Lean 作为一门通用编程语言所需要的。

*Litex-to-Lean 编译器还为 Litex 的严谨性提供了重要的独立保障。* 当前 Litex 仅 `src/` 下的 Rust 源码就超过 21 万行，并且随着数百条 builtin/infer rules 和新能力持续增长；审核如此大的可信实现面，天然比审核 Lean 精小得多的 kernel 更困难。当一条 Litex 验证路径能够被完整编译为 Lean 证明并由 Lean kernel 接受时，就为这条已覆盖路径提供了强而独立的正确性证据，显著降低了对 Litex 自身大型实现的单一依赖。

_这仍然是 Litex 正在实现和检验的目标，而不是当前 beta 版本已经全面达成的能力。现阶段的 Litex-to-Lean 编译器仅覆盖部分验证路径。编译器的第一性原理和框架已经建立，但细节上仍需进一步完善。我欢迎社区的反馈和贡献。_

<details>
<summary><strong>延伸阅读：Litex 到 Lean 的编译器如何工作</strong></summary>

*本节进一步解释实现机制与当前正确性边界；跳过它不影响后续正文。*

Litex是基于集合论的语言。Lean的Mathlib中包含了集合论的包。Litex的验证机制只是帮用户省去了自己写tactic的步骤。但这些步骤都会被保留在litex的输出中，哪怕这些步骤再多再复杂，它们的每一步都能对应到Lean的某些个tactic。所以从第一性原理上，Litex就应该能被编译成Lean。

实操上来说，Litex需要和Lean的Mathlib建立一个映射关系。验证机制的编译上，Litex-to-Lean编译器的工作就是把Litex中的每条验证路径映射到Lean中的对应的tactic。数学对象的编译上，Litex-to-Lean编译器的工作就是把Litex中的每个数学对象映射到Lean中的对应对象（当然不是直接翻译，而是设计一些wrapper作为中介）。这个映射关系是可行的，但需要时间打磨。这个中介代码在 https://github.com/litexlang/golitex/blob/main/lean/Litex/Core.lean ，还在持续完善中。这里给一些示例

```litex
forall s, S set, x s, f fn(y s) S:
    f(x) = f(x)
```

这个例子是说，f是从集合s到集合S的函数，x是s中的元素。然后f(x) = f(x)

```lean
-- Generated by compiler from 4_FunctionSet.lit. DO NOT EDIT.
import Litex

set_option linter.style.nameCheck false

namespace __Compiler_4_FunctionSet

theorem __fact0 :
    ∀ (s : Litex.Set) (S : Litex.Set) {__carrier0_3 : Type} (x : __carrier0_3) (__h0_3 : Litex.In x s) {__carrier0_4 : Type 1} (f : __carrier0_4) (__h0_4 : Litex.In f (Litex.fnSet (s : Litex.Set.{0}) (S : Litex.Set.{0}))),
      Litex.Same (Litex.fnApply f __h0_4 x (__h0_3)) (Litex.fnApply f __h0_4 x (__h0_3)) := by
  intro s S __carrier0_3 x __h0_3 __carrier0_4 f __h0_4
  exact Litex.Same.refl (Litex.fnApply f __h0_4 x (__h0_3))

end __Compiler_4_FunctionSet

```

这个编译器首先面对一个理论问题：如何在 Lean 和 Mathlib 中表示 Litex 的数学。同一个数学对象或语句往往有多种表达相同数学含义的 Lean 写法，而具体选择会长期影响生成代码能否自然复用 Mathlib、Litex 后续功能如何扩展，以及 Litex 与 Lean 两个生态如何协作。因此，函数、集合、成员关系和良定义性等基础概念需要一套一致且可持续的表示方式，而不只是让眼前的示例通过。

第二个是实践问题：如何把 Litex 内核成功执行时产生的信息变成 Lean 证明。Litex 验证会沿一棵搜索树把目标拆成更小的子目标；成功分支必须把所用规则、事实、数学对象、各子目标的证明和良定义性结果，以结构化信息从叶子返回根节点。语句执行中产生的声明、对象、事实和作用域变化也需要一并保留，使编译器能够确定性地重放 Litex 已经找到的验证路径，而不是从显示文本重建证明，或让 Lean 另行搜索证明。

</details>

<a id="conclusions"></a>
## 总结

Litex 的目标是让形式化数学的书写和验证更接近日常数学思维。通过提供一套更接近数学家日常书写的语法和交互契约，Litex 试图降低形式化书写与审查的门槛，让数学文本变得可执行，并促进更深的数学理解和发现。

这里可以作一个类比：编程语言会不断建立新的抽象层。C 通常让程序员不必逐条安排汇编指令；
Python 等更高层语言又吸收了更多常规工作，包括大量手动内存管理，以及为大多数变量预先声明类型的要求。

在这个意义上，Litex 由数百条常见内置规则，加上按事实形状进行的匹配和替换，
试图成为常规证明衔接工作的一层抽象。Litex丰富的验证流程上的机制，Litex给用户提供的数学对象、数学语句（以及没有给用户提供的数学对象、数学语句），都可以被看做是让用户源码停留在数学思维实际发生的层级的尝试。Lean基于抽象类型论，它的功能强大，但细节很多。Litex 基于大家更熟悉的数学公理体系，更熟悉的验证思维，帮用户省去了很多不必要的细节。当然Lean也有它的优势：它的内核小、可组合性强、生态丰富。Litex 目前仍在发展中，Litex源码自身的严格性可以由编译到Lean来得到。

> 有趣的是，如果我们观察一段C代码的机器码，其实里面有相当多的噪音，几乎有一半是各种各样的地址信息；而Lean的代码也是有很多地方是在记录定理的名称（id）。Litex的源码则尽量让数学事实本身成为中心，减少了这些噪音。（个人观点）

随着人类与 AI 的协作逐步创造和积累更多数学知识，形式化系统也应当探索不止一种书写和验证这些知识的方式。仅从默认交互方向来看，Litex 在有限意义上可以被看作“相反的 Lean”。这条设计路线不是要取代 Lean，而是为人和 AI 如何编写形式化数学代码，提供另一条值得实践和检验的思路。

沿着这条思路，可以展望Litex 的价值会从三个彼此关联的层面来理解：

1. **首先降低形式化书写与审查的门槛。** Litex 尽量让形式化源码接近人能直接理解的数学，使作者和审查者可以直接检查其中的对象、前提、推理主干和结论。这对 AI 生成的源码尤其重要：verifier 能检查的是已经写下来的命题，而可读的语义让人能够判断这个命题是否忠实表达了原本的数学意图。
2. **再让数学文本变得可执行。** 当定义、引理和证明仍然可以作为数学叙述来阅读和审查时，它们也可以同时接受机器检查，并在不同文件和章节之间复用。这样，形式化验证才有机会逐步走近教材、教学和科学写作，而不只存在于面向专家的证明助手工程中。
3. **促进更深的数学理解和发现。** 当形式化语言让数学真正变得工程化；当越来越多的人接触到形式化语言，我相信，数学家、学生和 AI 都会在更深的层次上理解数学对象、定义、定理和证明之间的关系，并在此基础上加速数学发现，甚至创新新的数学范式。

相关链接

1. 如果想直接试用例子，并查看 Litex 生成的输出和知识图谱，可以访问 [litexlang.com](https://litexlang.com)。

2. 如果关注内核实现，可以查看 [golitex 仓库](https://github.com/litexlang/golitex)。

注：在当前研究阶段，Litex 以公开方式推进研究并说明项目目标，因此仓库会同时保留已经检查的成果、实验以及尚未完成的工作。*公开可见不等于宣称完成*；每项能力应以当前测试、带日期的状态说明、可信边界和已知限制为准。
