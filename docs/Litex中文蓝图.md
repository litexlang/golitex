# Litex：让数学自我验证的形式化语言

Created and maintained by Jiachen Shen.

官网页面: https://litexlang.com/doc/Litex中文蓝图

英文版: https://litexlang.com/doc/Litex_Blueprint

> **Litex 是一个实验性爱好项目，仍处于 beta 阶段。请预期会有边缘问题。**

> **核心定位。** Litex 是一门基于集合论、以事实为导向的形式化语言，用于书写可读且可机器检查的数学。
> 用户写下构成证明主干的数学事实；Litex 则通过事实匹配、等式替换、定义、量化规则与有界数学推理，
> 重建常规的局部证明依据。

## 目录

- [背景](#background)
- [从日常数学的工作流出发](#workflow)
- [一个完整的小对照：群的单位元唯一性](#group-comparison)
- [Litex 如何推进这些设计目标](#design-goals)
  1. [用户声明数学模式与结果，系统寻找具体证明依据](#goal-1)
  2. [以集合论式对象为表面](#goal-2)
  3. [语法面向数学推理](#goal-3)
  4. [既保证严格性，又有可读性和低门槛](#goal-4)
  5. [以事实为中心，自下而上建立证明](#goal-5)
- [Litex：通向 Lean 可信生态的简洁数学前端语言](#compatibility)
- [总结](#conclusions)
- [附录：Litex 为满足成功条件正在做什么](#appendix-conditions)

<a id="background"></a>
## 背景

Litex 是一门以对象和事实为中心的数学形式化语言。它试图降低形式化证明的学习、书写和阅读门槛，让人和 AI 能用接近日常数学的方式表达推理、促进理解、激发新灵感；与此同时，每条提交给系统的结论都要接受机器的严格检查。

### 从数学符号到 AI 时代的形式化语言

数学史上，重要的新符号体系往往不只是缩短书写；它们还会潜移默化地改变人们看见问题、组织推理和探索新方向的方式。印度—阿拉伯数字体系重塑了计算，莱布尼茨发展并推广的微积分记号让变化率、微分与积分之间的关系更容易被表达和操作。到了近现代，TeX 和 LaTeX 虽然首先解决的是数学排版问题，但也通过稳定、通用的表达方式，改变了数学知识被书写、交换、发表和复用的方式。

今天，AI 正在让数学证明候选的生成变得更广泛、更规模化。当证明不再只是少数人手工写下的文本，关键瓶颈也会从“能否生成一段看起来合理的论证”，逐渐转向“能否可靠地检查、复用和积累它”。这使得形式化语言的价值更加突出：它有望像 LaTeX 之于数学排版那样，逐渐成为数学基础设施中不可或缺的一层——不仅让证明能被机器读取，更让它们能被机器严格检查。

Litex 想做的，就是让这层技术走近寻常学习者和数学使用者。它追求的理想是：**懂得什么数学，就能用形式化语言表达什么数学。**例如，一个已经掌握中学数学的人，应当能在很短时间内学会用 Litex 表达相应的定义、推理和证明，而不必先成为证明助手专家。这仍是 Litex 要用可运行示例、学习成本和真实使用不断检验的设计目标，不是当前 beta 版本已经全面实现的承诺。

要理解这个目标为何需要不同的语言设计，可以先看形式化证明与日常数学常见工作流之间的关系。

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
- **checker / verifier（检查器）**：对“负责检查”的程序部分的宽泛称呼。Litex checker 不仅核验对象是否良好定义，还会从内置规则和当前上下文中寻找事实的验证依据，因此它不能直接等同于 Lean 的 kernel；本文后面所说的 Litex 可信边界——也就是系统正确性所依赖、必须信任的部分——也相应更大。

可以先把两种流程简化成：

```text
Lean：命题 → Goal → tactic 与 elaboration → proof term → kernel 检查
Litex：对象和事实 → checker 检查并寻找依据 → 已验证事实扩展上下文
```

</details>

<a id="workflow"></a>
## 从日常数学的工作流出发

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

在下面两个默认交互维度上，Litex 与 Lean tactic 的推进方向恰好相反；这里的“相反”只描述默认工作流的方向，不是对两种系统整体能力的判断。

1. **Litex 证明自下而上；Lean tactic 证明自上而下。** 在 Litex 中，每条已验证事实都会扩展上下文，直到积累的事实足以支持结论。Lean tactic 证明通常从最终 Goal 出发，沿反向推理逐步把它转化为新的 Goal，直到能够由已知事实关闭。

   > 可以把写证明想象成搭乐高：一开始，我们拿到一批可用的积木，以及一个已经完工的成品；任务是证明这些积木确实能够搭出那个成品。Lean tactic 的默认做法像是从目标成品出发，一步步把目标拆了，拆到最后发现拆出来的乐高能和我们可用的积木匹配上，就算证明成功。Litex 的默认做法则像是直接拿起手上的积木一步步拼，直到形成一个和已经完成的成品一样的成品。这里不固定具体的拼接顺序：我们可以从不同角度、按不同次序拼接，只要最终形成目标成品。这个比喻只说明步骤顺序较为自由，并不表示 Litex 的验证标准更宽松。

2. **Litex 用户声明 *what*：“什么应当成立”；Lean tactic 用户声明 *how*：“应当怎样证明 Goal”。** Litex checker 寻找能与结果匹配的证明依据，并解释找到的验证路径。Lean 的 elaboration（细化）过程按照用户的 tactic 指令构造对应的 proof term，Infoview（目标窗口）显示变化后的 Goal，kernel 检查该 term。

   > 一份完整的乐高说明书同时包含两类信息：第一，这一步应当怎样拼；第二，这一步完成后，整个半成品应当是什么状态。Lean tactic 源码主要记录第一类信息——下一步怎样操作 proof state（证明状态；沿用上一维度的类比：记录的是这一步我们是怎么拆乐高的）；Litex 源码主要记录第二类信息——这一步推理后得到了什么数学事实（沿用上一维度的类比：记录的是这一步我们是怎么拼乐高的）。

这两个比喻描述的是默认接口的重心，而不是绝对的能力边界。Lean 的机制提供了非常灵活、通用的 proof-programming（把证明对象作为程序构造）环境；Litex 则有意选择范围更窄的默认交互，希望让初学者更容易开始写证明，也让源码更接近日常教科书的数学写法。Lean 也支持向前推理，Litex 也提供显式的目标导向（goal-directed）证明形式。后文的对照和五个设计目标，会继续展开这两种工作流的异同及各自的取舍。

> **比较说明。** 下文仍以 Lean 为贯穿全文的主对照，因为它能最具体地
> 显示 Goal-first 与 fact-first 的差异。文中对 Mizar、Isabelle/Isar、Rocq、
> ACL2 和 Naproche 的引用，用于说明 Litex 在现有设计空间中的位置：Litex 是独立设计的，
> 并非从这些系统派生而来。引用它们是为了说明邻近思路和最终形成的差异，
> 不表示直接的思想影响关系。

<a id="group-comparison"></a>
## 一个完整的小对照：群的单位元唯一性

群的单位元唯一性例子把上面两个工作流差异具体化：谁声明结果，谁补出证明路径，以及证明是从最终 Goal 向下分解，还是从已验证事实向上生长。这个对照例子还展示了定义和证明如何按数学顺序出现，以及结构和载体如何以显式的集合论对象呈现。

### Lean：显式的 record 结构、假设名和证明脚本

record 是由若干命名字段组成的结构；这里的 `Group` record 把群的载体、运算和公理打包在一起。proof script（证明脚本）则是定理 `by` 之后逐步写出的证明指令。

下面的 Lean 代码使用显式的 `Group` record。在较早的对照稿中，`calc` 的第一行把 `hright G.one` 用在了 `e = G.mul e G.one` 上；但该假设实际给出的是 `G.mul G.one e = G.one`。下面是与该假设匹配、可通过检查的改写：

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

这段修正后的 Lean 证明清楚地写出了 proof term 所需的步骤。这里 `hleft` 只是在陈述“`e` 是双侧单位元”时保留下来，最终结论实际只需要候选 `e` 的右单位律和 `G.one` 的左单位律。

下面的 Litex 版本用另一种表面语法表达同一个结构和唯一性论证。两段代码之后的五个正式小节会统一解释设计差异，并在每节末尾把一般论点对应回这个例子。

### Litex：结构、局部事实和结论顺着数学叙述写

下面的 Litex 片段已经用 Litex runner（执行并检查 `.lit` 文件的运行模式）验证通过。

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

有了这组代码对照，下面五个小节将依次解释其中的设计差异，并在每节末尾回到这个例子。这样，代码对照和设计论证会始终保持同一套对应关系。

<a id="design-goals"></a>
## Litex 如何推进这些设计目标

<a id="goal-1"></a>
### 1. 用户声明数学模式与结果，系统寻找具体证明依据

Litex 的默认取向是“模式优先，操作随后”：源码保留可复用的数学结构和应当成立的结果，checker 为当前实例寻找并解释具体证明依据。这种默认取向首先改变的不是代码长度，而是用户与系统的分工。用户写出 `1 + 1 = 2`、有限集的并仍是有限集、`x^2 >= 0` 这类应当成立的结果；Litex 先检查这些结果所涉及的对象是否良好定义，再从内置验证规则（builtin rules）、已知事实和已知的全称事实中寻找依据。在典型的 Lean tactic 交互中，结论先作为 Goal 给出，用户再逐步指定应当调用什么事实、如何改写或如何分解它，系统据此构造完整的证明。

一个很小的集合命题就能看出这种分工。如果 `s` 是 `t` 的子集，那么 `s` 与 `u` 的交集仍然是 `t` 与 `u` 的交集的子集。Litex 用户可以直接写下这个结果：

```litex
forall s, t, u set:
    s $subset t
    =>:
        intersect(s, u) $subset intersect(t, u)
```

这不是一个留待补全的证明空洞，而是交给 checker 检查的完整事实。这个事实的日常数学读法就是：取 `intersect(s, u)` 的任意成员 `x`，`x` 同时属于 `s` 和 `u`；由 `s $subset t` 可知 `x` 也属于 `t`，因而属于 `intersect(t, u)`。用户声明应当得到的数学结果，checker 负责从交集成员的展开、成员关系沿子集的传递，以及右侧交集成员的重新组合中寻找验证路径。

*Mathematics in Lean* 的集合章节给出了一个显式展开版本：

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

Lean 也能把同一证明写成更精巧的 proof term：

```lean
example {α : Type*} {s t u : Set α} (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩
```

两种 Lean 写法分别展示了显式控制和精巧泛化；后一种甚至更短，并通过 `α` 覆盖任意载体类型。所以差异不在行数，而在默认起点：Litex 鼓励用户先问“下一条应当成立的事实是什么？”，然后直接写下它，不必先掌握 `subset_def` 一类库中定义名或 proof-term 构造。这种默认起点降低了入门门槛，也让源码更接近日常数学书写。代价是，这些常规推理被移入 Litex checker，因而必须持续测试和审计。

把这个例子推广到更一般的交互层面，可以得到下面的分工：

| 默认交互 | 用户源码主要写出 | 交互输出主要补出 |
|---|---|---|
| Lean tactic + Infoview | 如何改写、分解或关闭当前 Goal | 每步之后当前还剩哪些 Goal |
| Litex 事实 + checker output | 下一条应当成立的事实或结果 | 该事实为什么通过，以及直接的验证来源 |

简化地说，Lean 的 tactic 源码偏向写 *how*，Infoview 补出 *what remains*；Litex 源码偏向写 *what*，checker output 补出 *why/how*。这是两种默认交互的重心差异，不是排他性的能力划分：Lean 也能显式写中间结果，Litex 也能组织带 Goal 的证明。

不过，只有当 checker 确实能够识别这些常见模式时，这种分工才有实际意义。人做数学时经常先认出模式：当前式子和之前的式子相同，或只差一次代入、一次展开、一次实例化。很少有人主要靠记住每一个辅助定理的内部名字来推理。

Litex 目前把数百条这类小而具体的数学模式放在内置验证规则中，覆盖数、等式、序、集合、函数、元组和成员关系等常见情形。这些规则并不构成一个不可见的“大自动化按钮”：每条规则都应当有可读的数学含义、对应实现和测试，并在输出中给出可检查的验证理由。Litex 的具体规则目录会随版本演进，因此这里不把“规则数量”当作稳定的宣传指标。

为每条内置规则提供对应的 Lean 定理或代码层面的解释，是一个有价值的审计目标；但一条规则不能仅仅因为看起来直观，就被视为已经获得形式化论证。可信边界、规则实现、回归测试和独立交叉检查都需要持续保持可见并不断完善。

除此之外，Litex 会把已经验证的事实放进当前上下文，并尝试用这些事实进行匹配和替换。已知的 `forall` 事实在参数条件满足时可以被实例化；已知等式也可以帮助较大的表达式匹配。这不是“猜测证明”：每个最终被接受的结果仍须通过规则和上下文检查。对于结论规模较大、检查成本较高，或需要读者明确看见依赖的结果，Litex 仍保留具名 theorem 和显式 `by thm` 调用。

#### “自动验证的魔法”实际上做了什么

简短的答案是：一套精细而有界的匹配—替换引擎。当用户提交一条事实时，
Litex 并不是把它交给一个无约束的证明器，让它随意发明一份证明。具体调度会因事实的
形状而异，但常规验证过程可以理解为下面这条有界的级联路径：

1. **先检查语义。** 确认当前事实里的对象、函数调用、成员关系、绑定参数和其他组成部分都良好定义。
2. **筛出可能相关的局部依据。** 根据事实的关系或谓词头，以及各参数的形状，在已知事实、已知 `forall` 事实、定义和 builtin rule schema 中缩小搜索范围。
3. **匹配结论并绑定参数。** 把候选结论与用户提交的事实做结构匹配。模式中的 `a` 可以因此绑定为 `identity` 这样的具体对象；同一参数重复出现时，每处必须匹配同一对象。
4. **实例化并检查条件。** 把这些绑定代入候选规则的参数类型、domain 条件和前提，再通过该路径所允许的检查，确认得到的具体条件。
5. **跨过小的表达差异。** 如果两边并非逐字相同，尝试翻转等式方向、沿已知等式进行运输与替换、直接计算、有界符号规范化、结构同余，或回放一层已检查的定义。
6. **带依据地提交结果。** 只要有一条有界路径成功，就记录它的直接来源，把新事实存入上下文，并应用相关 infer rules。如果所有路径都失败，系统返回 `unknown`，而不是悄悄发明一份证明。

这条级联路径的重要之处在于，可复用模式不只有一个来源。它可以来自
builtin rule catalog，也可以来自用户已经证明并放入当前环境的 `forall` 事实。
两者的验证来源不同，中心操作却是同一个：匹配当前结论、选出代入，再检查
实例化后的条件。

先看一个很小的 builtin rule 例子：

```litex
forall y R:
    0 <= abs(y + 1)
```

catalog 中已有 schema `forall x R: 0 <= abs(x)`。面对 atomic conclusion
`0 <= abs(y + 1)`，结构匹配会选出 `x := y + 1`；然后 checker 从带类型的
binder 和算术规则确认实例化条件 `y + 1 $in R`。详细输出会直接写出被选中的
catalog entry `order.abs_nonnegative` 及其 subgoal，而不是用一个泛化的“自动化”标签把匹配藏起来。

再让这个可复用模式来自用户自己的证明：

```litex
thm abs_zero_or_one:
    ? forall x R:
        x = 0 or x = 1
        =>:
            abs(x) <= 1
    by cases:
        ? abs(x) <= 1
        case x = 0:
            abs(x) <= 1
        case x = 1:
            abs(x) <= 1

abs(1) <= 1
# Or explicitly: by thm abs_zero_or_one(1)
```

第一段定理只检查一次，它的 `forall` 事实随后被存入环境。后面的 active line
只有 atomic fact `abs(1) <= 1`，没有 `claim` 外壳，也不要求 `by thm`。紧随其后的注释说明：
如果用户希望显式点名依据，也可以改写为 `by thm abs_zero_or_one(1)`。这条事实与已存结论
`abs(x) <= 1` 具有相同的结构形状：匹配选出 `x := 1`，然后检查实例化后的类型与前提。

不过，这个刻意选得很具体的例子有一个 provenance 细节：`abs(1) <= 1` 本身也可以直接计算，
因此当前 checker 会先走 builtin `number comparison` 路径，而无需再使用已存的 `forall`。
这条全称事实仍然是可匹配的局部依据，但不是这次运行实际选中的直接来源。
因而，这里展示的是多条 local justification 同时可用，而不是声称 checker 对这一行记录了
`cite forall fact`。相比之下，注释中的 `by thm` 写法会显式选择这条具名定理。

因此，builtin rule 与用户证明的全称事实，并不是两套互不相关的自动化机制。
它们进入同一套有界的“匹配—代入—检查”架构，同时又在验证依据中保持可区分：
一个引用 builtin rule，另一个引用先前已经证明的事实。像在 `Group` 中应用单位律这样的
结构化例子，只是把同一想法扩展到了更丰富的数学对象上；它增加的是 `struct` 与载体记号，
而不是一套新的验证原理。

所谓“魔法”，本质上是围绕候选索引、规范的结构匹配、能感知等式的替换、有界数学规则和验证来源，
所做的精细工程。它比逐字符串匹配更强，但又比无限制的证明搜索更受约束、更容易审计。

#### 隐去机械性的证明工作，保留数学思维的主干

这里可以作一个有限的类比：编程语言会不断建立新的抽象层。C 通常让程序员不必逐条安排汇编指令；
Python 等更高层语言又吸收了更多常规工作，包括大量手动内存管理，以及为大多数变量预先声明类型的要求。Litex 的实现并不等同于
这两类语言，这个类比也不意味着数学类型会消失。Litex 借鉴的只是一种更一般的设计思路：
可重复、可机械分类的工作，可以被移入语言系统，让用户把注意力放在当前层级真正重要的区分上。

在这个有限意义上，Litex 由数百条常见 builtin schema 构成的 catalog，加上按事实形状进行的匹配和替换，
试图成为常规证明衔接工作的一层抽象。从概念上看——而不是对每个实现数据结构的字面描述——
它可以被理解为一棵经过人工整理的大型分派树：常见的事实形状被预先分类，checker 再尝试相关的有界路径。
这种设计的实际期望是：当某些操作对当前数学步骤并无多少实质内容时，用户不必反复点名初等辅助定理、
选择常规改写方向、实例化显然的参数，或重述类型与良好定义性的常规后果。源码因而可以更突出定义、实质性条件、
关键中间事实和结论。

这仍然是一项边界需要继续检验的设计目标，而不是声称 Litex 已经准确找到了“哪些东西应该隐去”的最终答案。
从源码中隐去的工作并没有消失：builtin rules 会扩大可信边界，仍然需要实现审查、测试和独立复核；
checker output 应当继续展示实际选中的验证来源；当某条依赖对作者很重要时，用户仍可以用 `by thm` 等形式显式指定路径。
这种简化所试图做的，是把常规工作移入 checker，而不是把严格性移出系统。

#### 在数学被书写的层级完成验证

实际数学工作中的大量推理，都在当前抽象层级上使用已经建立的事实。
同一套机制也能扩展到结构化理论：在前面的 `Group` 例子中，
`identity = G.mul(G.one, identity)` 这一步就在单位律所在的数学层级上接受检查。
额外的载体和 `struct` 记号改变了当前可用的事实，却没有改变底层的匹配原理。
在常规验证路径中，Litex 不会先要求把这个局部步骤降为基础层的 proof term；
它直接尝试相关事实的实例、等式替换、定义和有界的数学规则。

这与 Lean 的最终接受路径不同，尽管 Lean 源码同样可以写在很高的层级。Lean 的
elaboration 会把面向用户的语法和 tactic 结果转换为
[core type theory 中的 term](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)，
再由 kernel 检查。Lean core term 可以保留 defined constant 和 opaque constant，所以这并不意味着
Lean 每次使用一个数学概念时，都会完全展开它的全部历史。更准确的差异是：
只要一条可信的高层路径已经接受当前事实，Litex 的常规验证就可以结束，不需要先为这个
具体实例构造一份完整的 kernel proof term。

因此，这里的性能假设针对的是 *foundational depth*（与基础逻辑相隔的层数），
而不是声称验证时间恒定。Litex 的目标是让常规交互成本更多取决于局部证明邻域的宽度——
相关事实和规则的数量、大小与歧义程度——而不是这条事实距离数学基础有多少层。
搜索分支、上下文规模、表达式大小、计算和规则前提的递归验证，仍然可能让检查变得昂贵。
所以，这套架构是否会在某类数学上形成相对 Lean 的显著速度优势，是一个需要 benchmark
回答的问题，而不是仅凭语言设计就已经得到的结论。

在编译器的设计模型中，每次成功验证都对应一条带有递归结构的证明路径，而且这条路径原则上应能被完整记录；Litex-to-Lean 编译器的目标，是把这条路径翻译成 Lean proof term，再交给 Lean kernel 独立检查。

<details>
<summary><strong>延伸阅读：Litex 到 Lean 的编译器如何工作</strong></summary>

*本节进一步解释实现机制与当前正确性边界；跳过它不影响后续正文。*

下文会用到三个编译器内部术语：`proof IR` 是记录证明树的中间表示，`FactId` 是已存事实的内部编号，`normalization`（规范化）是把某些书写不同但可判定相等的表达式整理为可比较形式。它们都不是 Litex 用户写证明时必须使用的语法。

从编译视角看，checker 为一条 Litex 事实的成功验证所选定的依据，本质上构成一棵可以递归展开的证明树：引用已有事实、引入 `forall` 参数与前提、等式替换、定义展开、计算和 builtin rule 都是树上具体的验证步骤，一个步骤也可能继续分成多个分支。Litex-to-Lean 编译器的目标不是在验证结束后重新阅读源码并“猜”一组 tactic，而是记录 checker 已经找到的验证路径，再把其中每个受支持的节点降为 Lean proof term——必要时表现为若干条 tactic——交给 Lean kernel 独立检查。例如，下面这条 Litex 全称事实说：如果 `a != c` 且 `a = b`，那么 `b != c`：

```litex
forall a, b, c set:
    a != c
    a = b
    =>:
        b != c
```

对于当前 MVP（最小可用原型）已支持的这条等式改写路径，编译器会生成下面的 Lean 代码（具体的 fact ID 由运行时决定）：

```lean
import Litex.Rules

theorem __fact19 :
    ∀ (a : Litex.Object) (__h0_1 : Litex.IsSet a)
      (b : Litex.Object) (__h0_2 : Litex.IsSet b)
      (c : Litex.Object) (__h0_3 : Litex.IsSet c)
      (__h0_4 : a ≠ c)
      (__h0_5 : a = b),
      b ≠ c := by
  intro a __h0_1 b __h0_2 c __h0_3 __h0_4 __h0_5
  exact by
    simpa only [__h0_5] using __h0_4
```

这段 Lean 代码把 Litex 自动找到的验证路径逐层展开了出来：`__fact19` 携带当前运行环境 `env` 中存储的 Litex `FactId`。共享的 `Litex.Rules` Lake 模块提供唯一的 `Litex.Object` 宇宙，生成文件检查 ABI 版本 8，不再重复 semantic core。每个源参数都是 `Litex.Object` 的值，后面紧跟它精确保留的 `Litex.IsSet` 参数事实。编译器生成的名字统一使用 Litex 源码保留的 `__` 前缀；assumption 命名为 `__h<forall-层深>_<层内顺序>`。每层 `forall` 里的参数事实和 domain 前提按源码顺序共用一个计数器。两个 domain 事实按源码顺序引入，最后的 `simpa only` 沿已保留的等式 `a = b` 把 `a ≠ c` 运输成 `b ≠ c`。相应的 proof IR 记录了 `forall` 引入、每个参数与 domain 的 `FactId`、一次正向等式改写，以及这些节点之间的递归依赖。因此，这不是编译器事后偶然猜中了一段 Lean tactic，而是 checker 已选中的验证依据被显式地重新表达成了 Lean 证明。

使用已知 `forall` 时也会按同样的方式展开。IR 会保留每个绑定参数实际选中的 Litex 对象、该对象的参数类型检查、每个命题形式的前提，以及直接代入后得到的结论。Lean 会把选中的对象具名化为 `proof_arg_2_1` 这样带类型的局部名字，把命题前提复读成 `proof_fact`，再给直接的定理应用取名。如果这个直接实例与目标并非逐字相同、而只是在有理表达式层面上相等，外层的 normalization 节点会再单独命名最终结果并检查这次转换。因此，一次代入不会被压成一行看不出过程的 `factN ...`，匹配器判定的相等也不会被默认成 Lean 里的定义相等（仅靠展开定义和计算即可相同）。

对于 builtin rule、已知 `forall` 的实例化、计算以及更深的组合证明，proof IR 也应当递归保留相应依据和分支。Litex 为常见数学对象提供了丰富的自动验证路径；一旦某条成功路径被选定，其中每一步都有明确依据，并且应当可以被记录和重放。当前 Litex-to-Lean MVP 只覆盖其中一部分路径；编译器遇到当前尚不支持的规则时，会停止此次编译，而不会退化成隐式 `axiom`（公理假设）、`sorry`（未完成证明的占位符），或伪装成已经证明。因此，“每条 Litex 验证都能编译成 Lean 并由 Lean kernel 接受”目前是正确性工作的目标，而不是已经完成的事实；当编译覆盖范围足够完整、翻译保持语义且编译器本身经过审计时，这条路径将能为 Litex 的验证结果提供很强的独立正确性保证。

> **当前边界：** Litex 到 Lean 的编译器仍在设计和实现中，尚未经过大规模测试。随着后续 Litex 内核和编译器继续迭代，同一段示例代码所生成的 Lean 代码也可能发生变化。欢迎交流。

</details>

在 `Group` 例子中，运算规律直接写在 `<=>:` 里，唯一性证明则直接写成 `identity = G.mul(G.one, identity) = G.one`。
此时，checker 寻找相应的单位律实例和等式方向，因此源码负责声明“什么成立”，验证路径负责说明“为什么成立”。

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

<a id="goal-2"></a>
### 2. 以集合论式对象为表面，而不是要求用户先学习类型宇宙

明确了用户与 checker 的分工后，下一个问题是用户在源码中直接面对什么样的数学对象。

Litex 的表面语言把对象、集合、成员关系、函数和结构都作为普通数学对象来写：对象属于集合；结构是带命名视图的笛卡尔积子集；性质由谓词表达。`s set` 表达的是“`s` 是一个集合”这一数学判断，不是在用户面前再叠一层必须操作的 `Type`、universe（用于组织“类型的类型”的层级）或 proof term。

这不表示语言完全没有约束。在当前实现中，函数参数的定义域、返回集合、结构字段和集合成员关系仍会被检查；只是这些约束尽量写在数学家本来就会写的位置。Litex 也保留了 `template` 等参数化构造，因为普通数学确实需要按载体、参数或假设索引的对象族；Litex 并不把自己描述成完整的依赖类型论（允许类型随对象参数变化的形式体系）。

`Group` 例子把这种集合论式表面具体展示出来：`s nonempty_set` 引入载体，`identity s` 表示成员关系，`G &Group<s>` 表示定义在该集合上的结构。
载体约束仍然明确，只是不先把它呈现为需要用户操作的 universe 层级。

> **设计空间中的位置。** 集合论式的表述并非 Litex 首创：
> [Mizar 的数学库](https://wiki.mizar.org/library/) 基于 Tarski–Grothendieck 集合论；
> [Lean](https://lean-lang.org/doc/reference/latest/The-Type-System/) 和
> [Rocq](https://rocq-prover.org/doc/V9.2.0/refman/language/core/index.html) 向用户展示依赖类型论内核；
> [Isabelle/HOL](https://isabelle.in.tum.de/website-Isabelle2024/dist/library/Doc/Isar_Ref/HOL_Specific.html)
> 使用多态高阶逻辑。Litex 的问题更具体地落在面向用户的对象接口上：
> 一套小型、以成员关系为中心的集合论式表层，能否在不要求用户先管理类型
> universe 的前提下，覆盖有实质内容的数学？

<a id="goal-3"></a>
### 3. 语法面向数学推理，而非函数式程序构造

对象的表层表示方式确定之后，还要决定证明过程以什么语法展开。

一个 Litex 文件的核心动作只有几类：定义对象或概念、检查事实、检查对象是否良好定义、在需要时给出 witness（存在性命题中的具体见证）、分类或归纳。在常见的顺序式写法中，用户可以按教材从前到后的顺序写：定义、条件、局部结论、下一条局部结论、定理。

这不等于 Litex 从不需要结构化证明。存在性、反证、分类讨论和归纳仍需要显式写出相应的数学动作。但日常的计算、代入和使用已知规律，不必被拆成“设定目标—调用 tactic—命名中间结果—再调用 tactic”的流水线。语言不应迫使用户为了迎合函数式 proof term 的构造顺序而重排一段本来清楚的数学叙述。

在 `Group` 声明中，乘法写成二元函数 `mul fn(x, y s) s`，使用时写成 `G.mul(x, y)`。
这种写法直接呈现数学上的二元运算，而不要求面向用户的表层语法先把它表示成一串柯里化的一元函数，也就是先固定一个参数、返回一个继续等待其余参数的函数。

> **设计空间中的位置。** 可读、声明式的数学语法同样有重要先例：Mizar 把形式化文章
> 组织成数学陈述与证明依据的序列，Isabelle/Isar 提供结构化的声明式证明，
> Naproche 检查受控自然语言。Litex 更具体的尝试是：能否用一套紧凑的 object–fact
> 语法，让一条有数学意义的陈述同时成为它自身的常规验证请求。

<a id="goal-4"></a>
### 4. 既保证严格性，又有可读性和低门槛

更接近日常数学的对象表示和证明语法，只有在不牺牲严格性的前提下才有意义。

表面接近教材不是放宽标准。在当前检查流程中，每条提交的事实都会得到 `true`、`unknown` 或 `error` 之一，其中 `unknown` 表示检查器没有从当前上下文找到足够依据，并不表示命题为假。检查流程区分表达式是否良好定义、当前上下文是否足够、以及具体是哪条 builtin rule、已知事实或全称事实支持了结论。`trust` 是显式接受一条未经证明的假设，不是证明；builtin rules（写入检查器的验证规则）和 infer rules（从已知事实自动推出新事实的规则）也属于可信计算基，也就是系统正确性所依赖、必须信任的实现部分。

所以 Litex 不是 Lean、Coq 或 Isabelle 的替代品。Litex 当前测试的是一种互补接口：一种范围更窄、可读性更强、以事实为中心的集合论式表面，能否让学生、领域研究者和 AI agent（智能体）以更低成本产生、检查和修复有用的形式化数学数据。这项接口实验是否成功，要由可运行示例、失败记录、测试、规则审计和独立检查来回答，而不是由语法看起来多自然来回答。

`Group` 片段只有在 runner 检查了字段、载体成员关系、结构规律的实例以及等式链的两段之后才会通过。
该片段不含 `trust`；如果显式加入 `trust`，这条未经证明的假设就会和 checker、builtin/infer rules 一样成为可信边界的一部分。

这条预期的快速路径与可信边界，其实是同一项选择的两面。Litex 能在高层验证路径
接受事实后直接结束，是因为这条路径上的规则实现属于可信边界。把记录的路径降为
Lean proof term，再由 Lean kernel 检查，会重新引入一条更慢、但更独立的审计路径。
这套架构让低延迟的局部检查变得可期，但它本身并不证明当前 Litex 在所有情况下都更快。

> **设计空间中的位置。**
> [Lean](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/) 和
> [Rocq](https://rocq-prover.org/doc/V9.2.0/refman/language/core/index.html)
> 把复杂的证明构造与负责检查最终 proof term 的 kernel 清楚分开。Litex 当前则把
> 许多数学 builtin/infer rules 放在自身的可信边界中，所以可读性本身不能成为
> 正确性论据。记录验证路径、审计规则、回归测试，以及逐步完善 Litex-to-Lean，
> 是这套接口寻求更强独立检查的途径。

<a id="goal-5"></a>
### 5. 以事实为中心，自下而上建立证明

前四点已经说明了用户与 checker 如何分工、用户面对什么对象、证明如何表达，以及严格性如何维持；最后一点转向证明如何随上下文向前生长。

Litex 是 fact-oriented（以事实为中心）的。它默认的推理单位是当前上下文中的下一条数学事实，而不是一个每行都必须立即推进的活跃 Goal。只要一条陈述位于当前作用域中、定义良好，并且能由现有上下文充分支持，checker 就可以接受它、保存它、应用当前适用的推理规则，并把增强后的上下文交给后续陈述。因此，Litex 的典型证明会向前、自下而上生长：先建立事实，由它们推出更多事实，直到积累的上下文足以支持最终结论。一条事实可以被紧接着的下一行使用，也可以被后续较远处的定理使用，还可以只作为一条独立的已检查结果。几条数学分支也可以先分别生长，再由之后的陈述让它们汇合。

Lean 通常的交互式定理证明是 goal-directed（以目标为中心）的，典型方向是向后、自上而下。最终定理先确定预期类型；局部 term（证明项）和 tactic 指令再在这个预期之下进行 elaboration，逐步把待完成的 Goal 分解或反推为更简单的子目标，直到 Lean 能组装出完整的 proof term。两者的默认问题可以概括为：Lean 问“为了构造当前 Goal，还必须证明什么？”；Litex 问“根据已经建立的上下文，下一条能够推出的事实是什么？”

这是默认工作流的差异，不是绝对的表达能力边界。Lean 可以通过 `have`、局部引理和独立的顶层定理积累前向事实；Litex 也可以用 `claim`、`thm` 等形式组织明确的目标导向证明。两种接口主要改变的是证明展开的方向，不是正确性标准：每条被接受的 Litex 事实仍然必须满足作用域、定义良好性和数学依据的要求。

下面这个局部重写例子可以更直观地展示这种方向差异。在 Lean 中，用户从待证明的 Goal 出发，用每条 `rw` 指定接下来调用哪个事实、按哪个方向匹配和替换：

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

这四个等号与 Lean 的四条 `rw` 恰好逆序对应。Lean 的代码告诉系统“下一步调用哪个事实、朝哪个方向改写 Goal”；Litex 的代码则告诉系统“如果这些推理能够完成，关键的中间结果应当是什么”。checker 再从当前上下文、等式匹配和结构规则中寻找每个相邻等式的依据。

因此，用户不必记住 `mul_assoc` 这样的库名称，也不必显式编排 `h`、`h'` 和结合律的调用顺序与方向，而是写出一条有数学意义的中间结果链。如果某一步等式跨越的推理过多，用户补充的也是中间表达式，而不是指导 checker 一步步怎样搜索。这个例子故意不使用一次完成整个代数推导的自动化，因为这里比较的不是代码长度，而是默认的证明交互方向。

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

Litex 则直接声明应当建立的中间结果和最终结果，checker 再从当前上下文中寻找它们的依据：

```litex
forall A, B, c set, x A:
    A $subset B
    B $subset c
    =>:
        x $in B
        x $in c
```

对应的 runner trace 把 Litex 源码没有写出的验证依据补出来；这里只摘录与两个结论直接相关的字段：

```text
"conclusions": [
  {
    "statement": "x $in B",
    "why_verified": {
      "type": "builtin rule",
      "rule": "membership through a known direct set inclusion"
    }
  },
  {
    "statement": "x $in c",
    "why_verified": {
      "type": "builtin rule",
      "rule": "membership through a known direct set inclusion"
    }
  }
]
```

在 Lean 中，用户告诉系统“下一步怎样证”，系统便把 `x ∈ c` 反向分解为 `x ∈ B`，再分解为已知的 `x ∈ A`。在 Litex 中，用户告诉系统“下一个结果是什么”，checker 则从 `x ∈ A` 出发，先确认 `x ∈ B`，再确认 `x ∈ c`。前者典型地从完整 Goal 向前提反向展开，是自上而下的；后者让可验证的事实逐步累积到结论，是自下而上的。

要进一步看清源码与输出如何互补，可以把 Lean 交互中的 Infoview 展开来看。Lean 源码没有把中间 Goal 写成定理内的数学陈述；光标沿 tactic 依次后移时，Infoview 把这一部分补出来。下面省略每一步都不变的 local context（局部上下文）：

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

因此，runner trace 与 Infoview 这两种输出恰好补足了两种源码各自没有写出的部分：Litex 源码已经写出 `x $in B` 和 `x $in c`，runner 报告它们为什么通过；Lean 源码写出了如何操作 proof state，Infoview 则报告每步之后还剩什么 Goal。

这两个例子也让“自下而上”变得具体：Lean 从完整 Goal 开始，逐步把它改写或分解到已知事实；Litex 则逐段建立可以确认的等式或成员关系，直到它们支持最终结论。日常数学书写往往也是先记录定义、已知事实和关键中间结果，再让它们汇聚成结论，而不是始终从一个形式化 Goal 出发，把它不断反向分解成子目标。对人和 AI 来说，提出有意义的中间表达式，通常也比持续记忆 `pow_two`、`mul_assoc` 一类库名称及其调用方向更自然。这种常见倾向并不表示所有数学发现或证明都严格自下而上；归纳、反证、存在性证明和复杂定理仍可能需要明确的目标结构。

回到 `Group`：结构规律在概念定义时先被验证并保存；候选单位元的规律随后扩展上下文；最后才检查单位元唯一性的等式链。
这个顺序正是上面计算链和集合包含例子共同展示的自下而上模式。

> **设计空间中的位置。** Mizar 和 Isar 已经支持向前展开的声明式证明文本，ACL2 会累积
> 可复用的定理数据库，Naproche 会逐步检查数学陈述。因此，“自下而上生长”本身并不是
> Litex 的差异化主张。Litex 真正检验的是这样一套组合：普通 fact 是能够扩展上下文的
> 可执行单元；local justification 不需要另行调用 proof method 就会启动；只有当
> 常规重建到达边界时，显式证明结构才出现。

<a id="compatibility"></a>
## Litex：通向 Lean 可信生态的简洁数学前端语言

Litex 首先是一门可以独立工作的形式化语言。它拥有自己的语法、运行时和 checker；一份 Litex 数学文档即使不编译成 Lean，也能直接接受 Litex 的良定义性检查、事实验证和局部证明反馈。因此，这里的“Lean 数学前端语言”不是说 Litex 只是 Lean 中的一层语法糖或必须依附 Lean 才能运行；它说的是 Litex 还能把自己已验证的数学编译成 Lean，因而作为一门独立源语言接入 Lean 的可信内核、Mathlib 数学库和工具链。

> **理想中，当 Litex 到 Lean 的编译逐步完善后，在 Litex 中写下的定义、定理和证明，都可以完整地带到 Lean 中，交给 Lean 再独立检查，而不需要用额外的公理填补缺口。这样，选择 Litex 并不意味着离开 Lean。你在 Litex 中完成的数学，仍然可以进入 Lean 和 Mathlib，继续被检查、引用和发展。即使你的目标是为 Lean 社区添砖加瓦，也可以先尝试用 Litex 帮助自己表达和推进数学：Litex 与 Lean 不必争夺你的时间，它们可以共同承载同一份数学工作。**

Lean 和 Mathlib 已经建立了强大的形式化数学基础。Litex 无意复制或取代这些成果，而是希望将自己的独立语言体验与这套成熟基础设施结合起来。

使用 Litex 时，用户可以把注意力放在数学对象、条件、中间事实和结论上，并从 checker 获得快速、局部而可追踪的验证反馈。这对 AI 同样重要：生成系统可以围绕“下一条应当成立的数学事实”进行小步建议，再根据 checker 返回的具体依据或失败边界继续修正，而不必一开始就把数学意图完全降解为 elaboration、类型类、命名空间和 tactic 调用的细节。这些机制是 Lean 表达力与可组合性的重要来源；Litex 要做的不是否定它们，而是让它们不必成为每个使用者进入形式化数学的第一道门槛。

*Litex-to-Lean 编译器还为 Litex 的严谨性提供了重要的独立保障。*

当前 Litex 仅 `src/` 下的 Rust 源码就超过 21 万行，并且随着数百条 builtin/infer rules 和新能力持续增长；审核如此大的可信实现面，天然比审核 Lean 精小得多的 kernel 更困难。当一条 Litex 验证路径能够被完整编译为 Lean 证明并由 Lean kernel 接受时，就为这条已覆盖路径提供了强而独立的正确性证据，显著降低了对 Litex 自身大型实现的单一依赖。

这使 Litex 不只是一套更短的语法，而是一种不同的交互契约：人和 AI 主要表达数学上“什么成立”，Litex checker 记录“为什么成立”，Litex to Lean编译器则必须保留实际的验证路径、作用域、事实引用、良定义性依赖和 `trust` 来源，再由 Lean kernel 复核导出的证明。

> **Litex 试图让形式化数学的入口更接近数学本身，同时让结果走向 Lean 已经建立的可信内核和广阔生态。即使你是10岁的数学从业者，也能从Litex出发，体会形式化语言的魅力和能量。**

_这仍然是 Litex 正在实现和检验的目标，而不是当前 beta 版本已经全面达成的能力。现阶段的 Litex-to-Lean 编译器仅覆盖部分验证路径。编译器的第一性原理和框架已经建立，但细节上仍需进一步完善。我欢迎社区的反馈和贡献。_

<a id="conclusions"></a>
## 总结

Litex 想做的并不是把证明省掉。更准确地说，它希望用户先写出自己真正想表达的数学事实，再由机器说清这些事实如何通过检查、依据来自哪里，以及可信边界在哪里。

沿着这条思路，Litex 的价值可以从三个彼此衔接的层面来理解：

1. **首先降低形式化书写与审查的门槛。** Litex 尽量让形式化源码接近人能直接理解的数学，使作者和审查者可以直接检查其中的对象、前提、推理主干和结论。这对 AI 生成的源码尤其重要：verifier 能检查的是已经写下来的命题，而可读的语义让人能够判断这个命题是否忠实表达了原本的数学意图。
2. **再让数学文本变得可执行。** 当定义、引理和证明仍然可以作为数学叙述来阅读和审查时，它们也可以同时接受机器检查，并在不同文件和章节之间复用。这样，形式化验证才有机会逐步走近教材、教学和科学写作，而不只存在于面向专家的证明助手工程中。
3. **让受阻的证明帮助改进推理与表述。** 当一段证明暂时走不下去时，清楚的受阻位置可以帮助我们判断：是推理路径还缺一个中间事实，还是形式化的数学表述需要调整。把这样的定位与修复过程保留下来，人和 AI 都能用它来改进下一次尝试。

这三个层面层层相接：可读性让审查成为可能，可执行性让数学能够积累和复用，清楚的受阻反馈则帮助改进下一轮推理。不过，它们并不会因为语法看起来像数学就自然实现。[附录](#appendix-conditions)介绍了 Litex 为满足这些条件已经开始的工作，以及目前仍然存在的边界。

在语言的运行层面，这条路线可以从一条普通数学事实说起：

> **在 Litex 中，local justification（局部证明依据的重建）不是用户需要调用的 tactic，
> 而是一条普通数学事实的默认执行语义。**

当用户写下一条不附带证明指令的事实时，这一行同时承担两个角色：它既是作者想保留下来的数学陈述，
也是要求 checker 从当前已检查上下文中重建常规依据的验证请求。这种双重角色会展开成一条完整链条：

1. **在语言表层，**普通事实直接触发验证，不要求用户先写 tactic 名、定理引用或 proof term。
2. **在 checker 内部，**相关的已知事实、等式、定义和适用的全称事实，会经过有界且理解数学对象的路径接受检查。
3. **验证成功后，**这条事实及其常规推论立即扩展后续上下文。
4. **在系统输出中，**checker 可以重新展示简洁源码中隐去的具体验证路径和来源。
5. **在常规重建的边界上，**见证、分类、反证、归纳和指定路径等显式数学证明过程仍然存在。

合起来看，这五点不是五项彼此独立的便利功能，而是一套默认的人机分工：作者写出证明的数学主干，
checker 补出其中常规的局部联系；只有当数学本身确实需要时，显式证明结构才进入源码。

从语言设计的角度看，这是一项仍需检验的抽象层假设：正如更高层的编程语言会吸收可重复的底层操作，
Litex 试图把可重复、可分类的证明操作变成 checker 的基础设施，使用户源码能够尽可能停留在数学思维实际发生的层级。

Litex 所主张的接口差异是这套分工，而不是孤立地拥有局部自动化。前文对相关系统的梳理
也表明，其中的单项机制各有先例。Litex 因而提出一个更窄、也更偏向整体架构的
研究假设：这个由事实触发的完整循环——而不只是
一个可选 tactic、一套引用约定或一个定理级证明器——能否成为一套小型 object–fact 语言在有实质内容且
可读的数学中的统一默认语义？

同一套分工也指向一种双路径验证架构：常规交互路径可以保留被提交事实所在的抽象层级，
主要为局部证明邻域付出成本；另一条审计路径则可以把记录下来的验证路线降为基础层 proof term，
交给更独立的内核检查。第一条路径目前是一项架构上的性能假设，而不是已有 benchmark 支持的
“在所有情况下都更快”的结论。

这样看，Litex 与常见 Lean tactic 工作流的差异就不是“有自动化”和“没有自动化”，而是自动化在默认源码
契约中的位置：Lean tactic 证明先声明 Goal，再调用证明方法；Litex 的普通事实只要被写下，就会启动常规的
局部依据重建。把这种人机分工说得更尖锐一些，就是：

> **说得尖锐一点：Lean 常见的 tactic 工作流，就像强制要求你读一本数学书时从最后一页开始读，写一篇论文时从最后一页开始写——先固定最终 Goal，再向后反推前面必须补出什么。**

对于数学探索、学习和教材式叙述而言，这种顺序可能会让部分读者感到很别扭。Litex 的设计判断是：这种从最终 Goal 反推的顺序，不应成为书写形式化数学时唯一或默认的方式。

不过，当 Litex 把具体证明操作移入 checker 时，压力也随之转向 Litex 自身的可信边界。

> **同样尖锐地说：从第一性原理看，Litex 当前最大的问题，是它的可信内核太大。Litex 把数百条常见证明模式放进 builtin 和 infer rules，把工作从用户的 proof script 移进了可信计算基。证明工作并没有消失，只是被系统吸收了。要让 Litex 的验证结果再由可信边界更小且相对独立的 Lean kernel 复核，Litex 还需要把记录的验证路径编译成 Lean proof term；这一编译覆盖目前尚不完整。**

*Litex 正在构建并完善 Litex-to-Lean 编译器，欢迎通过 GitHub 或邮件 litexlang@outlook.com 联系我进行深入交流。*

上面的编译目标回应可信性问题，但不需要放弃这种接口选择。更成熟的路径应当让 Litex 用户继续声明
*what*：“什么应当成立”，由 checker 重建局部验证路径；与此同时，导出的 Lean proof term 独立地重放并
检查这条路径。因此，接口主张和可信性策略必须放在一起：local justification 可以在源码中保持隐含，
前提是它所吸收的证明工作仍然可检查，并且越来越多地能够在 Litex 当前可信边界之外被重放。

随着人类与 AI 的协作逐步创造和积累更多数学知识，形式化系统也应当探索不止一种书写和验证这些知识的方式。仅从默认交互方向来看，Litex 在有限意义上可以被看作“相反的 Lean”：Lean tactic 通常从最终 Goal 出发，让用户描述如何构造证明；Litex 通常从已建立的事实出发，让用户描述下一个应当得到什么，再由 checker 寻找并解释依据。这条设计路线不是要取代 Lean，而是为人和 AI 如何编写形式化数学代码，提供另一条值得实践和检验的思路。

由于这条路线仍在研究阶段，当前仓库也应当按开放研究项目来理解：

> 在当前研究阶段，Litex 以公开方式推进研究并说明项目目标，因此仓库会同时保留已经检查的成果、实验以及尚未完成的工作。公开可见不等于宣称完成；每项能力应以当前测试、带日期的状态说明、可信边界和已知限制为准。

<a id="appendix-conditions"></a>
## 附录：Litex 为满足成功条件正在做什么

前面的三层价值，不能只靠一个可读的接口来实现。因此，当前 beta 正在六个相互关联的方向上继续投入，并用真实实现和数学语料检验它们。下面讲的是正在推进的工作，而不是已经完成的可靠性、可扩展性、易用性或性能证明。

1. **让可信边界清楚可见，并能逐步接受独立复核。** 可靠性的起点，是先说清系统究竟检查了什么、又没有检查什么。`trust`、`trust have` 和 `axiom` 都是显式源码形式；普通文件运行会报告尚未验证的导入，而 `-strict` 会验证配置依赖并拒绝这些可信形式。常规输出和详细输出会区分一条事实为何通过、什么进入了上下文、随后推断出了什么，以及出现了哪些直接可信语句。验证路径正在携带越来越结构化的证据，使部分路径可以由 Litex-to-Lean 编译器交给 Lean kernel 重放；尚不支持的路径会明确停下，而不会生成 `sorry` 或新公理。目前仍有需要继续完善的边界：Litex 会记录直接可信语句，但还没有为每条下游事实传播完整的传递性 trust 标签；Lean 重放也只覆盖已有文档说明的部分语言与 builtin rules。参见[系统地图](Litex_System_Map.md#reading-results-and-trust)、[CLI 可信控制](cli.md#global-options)和[编译器当前边界](../lean/README.md)。

2. **用长篇数学检验内容能否持续组合。** 可信边界说清之后，定义和证明还要能走出小例题、继续在更长的内容中组合。Litex 的模块系统为 import 和 export 规定了确定的数学顺序，同时支持聚焦的单文件检查和完整模块运行。已登记的多文件教材工作区，会在跨章节的真实依赖中检验定义、定理和命名空间的组合情况。这些实践能说明当前已经走到哪里，但更大规模的开发能否一直顺畅扩展，仍需要继续检验；参见[模块约定](cli.md#project-modules)和[教材工作区登记表](../scripts/.textbooks)。

3. **在保持简洁的同时，让验证过程仍然可检查。** 局部依据重建越方便，就越需要避免简洁源码变成无法说明的自动化。阅读视图与审计视图会展示直接的 `why_verified` 原因、良定义性和验证阶段、被引用事实、builtin-rule 前提与失败边界；关系图和事实图则从依赖角度补充展示这些路径。Builtin rules 以明确的数学模式和具名证据实现，并通过聚焦的正向回归与邻近负向边界接受审计。这些工具已经让 checker 吸收的更多工作变得可见，而规则审查和解释易读性仍需要持续完善；参见 [CLI 输出约定](cli.md)和[英文版附录 A](Litex_Blueprint.md#appendix-builtins)。

4. **降低并实际测量书写与审查的总成本。** 可信与可检查最终还要落到实际使用上：Litex 若要形成真实价值，写出和维护证明的总投入就必须相对现有方案显著下降。以事实为中心的语言表层、有界局部证明搜索、紧凑反馈、登记文件运行和持久化的 `-session -before` 工作流，都在尝试减少证明书写、修复和审查的投入与等待时间。要证明 Litex 相对成熟方案具有可信的同题端到端优势，还需要在代表性任务上测量作者时间、修复轮次、审查 AI 生成的形式命题是否忠实表达原意所需的投入、证明债务、运行时间和维护成本。

5. **让 Litex 的成果能够继续进入 Lean 生态。** 降低入门成本，不应以把新的数学内容留在一座孤岛上为代价。仓库已经包含部分 Litex-to-Lean 编译器、Lean 语义包装层、成对的生成示例和真实 Lean kernel 检查。对已经支持的路径，编译器会保留由 verifier 维护的事实身份、作用域、证明证据和良定义性义务；尚不支持的已验证语句会停在明确的拒绝结果上，而不会由系统补出一个凭空而来的证明。目前的覆盖范围仍然有限，因此互操作更准确地说是一条不断扩展的审计与迁移路径，而不是对所有内容的普遍导出保证；参见[通向 Lean 可信生态的简洁数学前端语言](#compatibility)和[编译器当前支持边界](../lean/README.md)。

6. **用真实数学工作反复检验这套设计。** 最后，前面这些条件都不能只在精心挑选的演示中成立。Litex 正在接受普通示例、多文件教材和数据集工作区的检验，其中包括 MATH500、miniF2F、中学数学以及更长的本科数学内容。数据集 runner、源工作区中的 todo、证明日志、trust 审计和最小回归用例，用来区分已经检查的结果与只完成翻译但仍有缺口的工作；它们也会保留那些推理路径还需要中间事实、或面向原问题的数学表述需要调整的案例。语料再多，也只有在每个条目的状态都说得清楚时，才能构成可信证据：一个条目只有在通过对应的登记 gate 后，才能作为已检查证据；混合状态或尚未完成的语料仍会保持明确标注。参见[英文版附录 B](Litex_Blueprint.md#appendix-examples)和[数据集 runner 源码](../src/main_test/lit_file_runner_tests/dataset_runners.rs)。

这六个方向放在一起，构成的是一项持续推进的工程与研究计划，而不是对“所有困难条件都已经解决”的宣告。只有当可信边界持续可审计、长篇数学能够继续组合、解释保持可检查、经测量的端到端成本真正下降、Lean 重放在不引入证明缺口的前提下继续扩展，并且数学原意与形式表达之间的偏差仍然清晰可见时，前述三层价值才会真正可信。

相关链接

1. 如果想直接试用例子，并查看 Litex 生成的输出和知识图谱，可以访问 [litexlang.com](https://litexlang.com)。

2. 如果关注内核实现，可以查看 [golitex 仓库](https://github.com/litexlang/golitex)。

3. 如果想查看用 Litex 书写的数学教科书，可以访问 [Litex 数学教科书](https://litexlang.com/textbook)。
