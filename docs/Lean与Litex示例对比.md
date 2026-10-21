# Litex 与 Lean：构造、理解和使用数学知识

由沈嘉辰创建和维护。

[在浏览器中尝试示例](https://litexlang.com/doc/Representative_Lean_Litex_Example_Comparisons) ·
[英文 Markdown 源码](https://github.com/litexlang/golitex/blob/main/docs/Representative_Lean_Litex_Example_Comparisons.md) ·
[English](Representative_Lean_Litex_Example_Comparisons.md)

数学语言影响作者写下什么、检查器重建什么，以及其他读者能理解和使用什么。本页围绕一个问题比较 Litex 与 Lean：

> **把一个数学想法变成可检查、可理解、可修复、可继续使用的知识，需要付出多少劳动？Litex 的设计改变了其中哪些工作？**

Litex 探索以事实为中心的数学语言：作者引入对象、定义概念、陈述事实，并给出有意义的证明步骤；检查器从已接受的上下文中建立受支持的连接。下面的例子让这种分工变得可见，并提出关于数学工作成本的可检验假设。目前的示例尚未证明跨任务的书写或阅读成本优势。

<a id="3-calculation-chains"></a>
<a id="3-计算链"></a>
<a id="direct-local-consequences"></a>
<a id="the-central-inversion-state-the-next-fact-reconstruct-its-grounds"></a>
<a id="核心倒置陈述下一条事实重建其依据"></a>
<a id="直接的局部推论"></a>
<a id="语法先写想要成立的事实"></a>
<a id="constructing-knowledge"></a>

## 1. 构造：源码多直接地表达数学路线？

解方程组 `2*x + 3*y = 10`、`4*x + 5*y = 14`。数学上的选择是：第一个方程乘二，再减去第二个方程，消去 `x`。

```litex
forall x, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14
    =>:
        y = 2 * (2 * x + 3 * y) - (4 * x + 5 * y) = 6
        x = ((2 * x + 3 * y) - 3 * y) / 2 = (-4)
```

源码保留消元步骤和求 `x` 的代入。Litex 用前提和代数规则检查每个连接：作者选择有用的计算，检查器提供常规步骤的依据。更长的证明仍需要作者选择中间事实、见证、估计或分情况。

Lean 可以通过 `calc` 保留同一条数学路线：

```lean
import Mathlib

example (x y : ℝ)
    (h1 : 2 * x + 3 * y = 10)
    (h2 : 4 * x + 5 * y = 14) :
    y = 6 ∧ x = -4 := by
  have hy : y = 6 := by
    calc
      y = 2 * (2 * x + 3 * y) - (4 * x + 5 * y) := by linarith
      _ = 2 * 10 - 14 := by rw [h1, h2]
      _ = 6 := by norm_num
  have hx : x = -4 := by
    calc
      x = ((2 * x + 3 * y) - 3 * y) / 2 := by ring
      _ = (10 - 3 * 6) / 2 := by rw [h1, hy]
      _ = -4 := by norm_num
  exact ⟨hy, hx⟩
```

若任务只要求完成定理，Lean 也可以使用更短的自动化证明：

```lean
import Mathlib

example (x y : ℝ)
    (h1 : 2 * x + 3 * y = 10)
    (h2 : 4 * x + 5 * y = 14) :
    y = 6 ∧ x = -4 := by
  constructor <;> linarith
```

这几种形式支持不同的比较。完成时间应使用各系统有效的惯用工具；阅读任务则可以询问读者能否从源码恢复消元论证。单独统计代码行数不能回答这两个问题：短自动化调用可以隐藏较长推导，较长计算也可能有意把推导留给读者。

Litex 在这里的特点，是下一条数学事实本身就构成检查请求。Lean 也支持前向 `have` 证明和自动化；其 [elaborator 构造证明项，再由内核检查](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)。比较应落在作者接口及其成本上，也包括作者希望对常规证明重建保留多少控制。

<a id="8-a-design-perspective-what-the-author-states-what-the-checker-reconstructs"></a>
<a id="8-设计视角作者陈述什么检查器重建什么"></a>
<a id="9-本地运行时对照非正式测量"></a>
<a id="leanlitex-代表性示例对比"></a>
<a id="representative-leanlitex-example-comparisons"></a>
<a id="six-related-changes-of-starting-point"></a>
<a id="why-the-combination-matters"></a>
<a id="为什么组合值得研究"></a>
<a id="六个相关的起点变化"></a>
<a id="comparison-dimensions"></a>

### 贯穿示例的六个问题

| 数学活动 | 比较问题 | 现有材料 |
| --- | --- | --- |
| [构造](#constructing-knowledge) | 从数学路线到被接受的源码，还需要做多少工作？ | 方程与估计链、见证。 |
| [保留含义](#meanings-and-domains) | 怎样让运算含义和使用条件与原问题保持一致？ | 除法、平方根、带条件函数。 |
| [积累知识](#objects-and-membership) | 一个对象怎样获得更多性质，并进入后续上下文？ | 数系成员关系、子集、交集。 |
| [修复](#interaction-and-repair) | 失败反馈揭示什么，之前接受的工作还能否使用？ | Session 交互、结构化反馈。 |
| [理解与复用](#understanding-and-reuse) | 别人能否识别路线、遵守条件，并继续做数学？ | 收敛证明、保持定义域的有理映射、主题模块。 |
| [反复检查](#checking-performance) | 工作流能负担多少次检查，依赖增长时成本怎样变化？ | 注明日期的本地计时、见证检查。 |

这些章节首先说明具体设计行为。[评价部分](#evaluating-the-comparison)区分已有证据和仍需开展的测量。数学基础、支持范围与信任则作为明确的[比较条件](#trust-and-scope)。

<a id="domains-carried-by-mathematical-objects"></a>
<a id="ordinary-mathematics"></a>
<a id="对象知道一个性质与打包一个子类型"></a>
<a id="数学对象携带的定义域"></a>
<a id="自然数减法"></a>
<a id="语义litex-走正常数学的路线"></a>
<a id="负数输入的实数平方根函数"></a>
<a id="除以零"></a>
<a id="meanings-and-domains"></a>

## 2. 含义：数学表达的使用条件在哪里检查？

给出有效证明与表达原本的数学，是两项分别需要保证的事情。Litex 希望让熟悉的运算含义和定义域直接出现在源码中。值得比较的是：这种设计是否帮助作者保留原问题，并发现遗漏条件。

### 除法与带条件调用

对于倒数，Litex 将非零条件写进定义域：

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

`reciprocal(0)` 不在该定义域中。接受使用 `1 / x` 的事实之前，检查器必须从当前上下文建立 `x != 0`；连 `1 / 0 = 1 / 0` 也会在良定义性检查处失败。

Mathlib 有意把标准实数除法扩展到零分母处：

```lean
import Mathlib

example : (1 : ℝ) / 0 = 0 := by
  simp
```

其 [`div_zero`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/GroupWithZero/Basic.html#div_zero) 不允许非法约分：`x / x = 1` 等规律仍要求非零前提。Lean 也能编码受限定义域。比较应考察条件在哪里表达、建立和使用，以及作者为保持原来的数学含义需要做多少工作。

用户自定义的条件也有同样的问题：

```litex
have fn nonnegative_input(x R: x >= 0) R = x

forall x R:
    x >= 0
    =>:
        nonnegative_input(x) = x
```

一种 Lean 接口用子类型打包值与证据：

```lean
import Mathlib

def nonnegativeInput (x : {y : ℝ // 0 ≤ y}) : ℝ := x.val

example (x : ℝ) (h : 0 ≤ x) : nonnegativeInput ⟨x, h⟩ = x := by
  rfl
```

Litex 在调用时检查已有的关于 `x` 的条件；子类型接口传入值和证明。Lean 也可以采用独立证明参数，自动化还能协助处理。实际任务可以测合法调用的构造成本、非法调用的诊断，以及修改定义域时能否保留原来的规格。

### 减法与实数平方根

Lean 的自然数减法在零处截断：

```lean
example : (1 : Nat) - 2 = 0 := by
  decide
```

Litex 对这个表达式保留通常的整数值减法：

```litex
1 - 2 = -1
1 - 2 $in Z
```

Lean 的 `Int` 也满足 `1 - 2 = -1`；这里的问题是选中了哪一种运算。参见 [`Nat.sub`](https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/#Nat.sub)。

Mathlib 的实数平方根在负数输入处返回零：

```lean
import Mathlib

example : Real.sqrt (-1) = 0 := by
  exact Real.sqrt_eq_zero_of_nonpos (by norm_num)
```

Litex 的实数平方根要求输入非负：

```litex
have fn real_root(x R: x >= 0) R = sqrt(x)
real_root(4) = 2
```

因此 `sqrt(-1) = 0` 在 Litex 中无法通过良定义性检查。Mathlib 的 [`Real.sqrt_eq_zero_of_nonpos`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Real/Sqrt.html#Real.sqrt_eq_zero_of_nonpos) 记录了一项主动扩展；其平方根恒等式仍保留相应定义域前提。这些例子确立了具体语义选择。要判断哪种接口更能减少规格错误，还需要独立固定原意的任务，并用合法对照测量不必要的拒绝。

<a id="5-set-theoretic-objects-at-the-surface"></a>
<a id="5-表层的集合论对象"></a>
<a id="intersections-preserve-inclusion"></a>
<a id="交集保持包含关系"></a>
<a id="objects-and-membership"></a>

## 3. 对象：数学知识怎样逐步积累？

在 Litex 中，同一个源码对象可以获得更多事实：

```litex
have a N = 1
a $in Z
a $in R
a $in C
```

每行并没有替换这个数。关于它属于不同数集的知识进入上下文，供后续检查使用。对象身份与知识积累因而直接进入源码模型。

Lean 通过类型与嵌入组织表示。例如：

```lean
import Mathlib

example : ((1 : ℝ) : ℂ) = (1 : ℂ) := by
  simp
```

经过嵌入，实数值与复数值相等。比较可以跟踪同一个数学值经过多个接口的过程，记录两边需要的转换、辅助证据与修复工作，也评估这些表示提供的保证与通用性。

集合提供了另一组具体例子：

```litex
{1, 2} $in {{}, {1, 2}}

{1, 2} $subset {1, 2, 3}
{1, 2} $in power_set({1, 2, 3})

forall A, B set, x A:
    A $subset B
    =>:
        x $in B
```

```lean
import Mathlib

example : ({1, 2} : Set ℕ) ∈ ({∅, {1, 2}} : Set (Set ℕ)) := by
  simp

example : ({1, 2} : Set ℕ) ⊆ ({1, 2, 3} : Set ℕ) := by
  simp

example {α : Type} {A B : Set α}
    (hAB : A ⊆ B) {x : α} (hx : x ∈ A) :
    x ∈ B := by
  exact hAB hx
```

Litex 源码直接使用集合与成员关系；Lean 源码用 `Set ℕ`、`Set (Set ℕ)` 和类型参数 `α` 标明环境载体。Litex 的 `forall x S` 引入属于 `S` 的对象；`forall A set` 引入集合参数，不是某个包含所有对象的全集的元素。

### 按数学内容使用已知事实

若 `s` 包含于 `t`，两边与 `u` 取交后仍保持包含：

```litex
forall s, t, u set:
    s $subset t
    =>:
        intersect(s, u) $subset intersect(t, u)
```

Lean 可以给出简短的逐元素证明：

```lean
import Mathlib.Data.Set.Lattice

example {α : Type*} (s t u : Set α) (h : s ⊆ t) :
    s ∩ u ⊆ t ∩ u := by
  intro x hx
  exact ⟨h hx.1, hx.2⟩
```

Litex 检查器完成常规的成员拆解与传递；Lean 证明通过 `hx` 和构造的配对显式给出这个论证。两边都可以在合适时使用命名定理。比较问题是作者怎样取得相关知识：陈述需要的事实、选择定理名称、使用自动化，或给出显式路线；以及上下文增长之后，这些方式能否可靠地继续工作。

这里比较的是源码接口。生成的 Lean 仍有类型，也需要认证后的表示桥接；详见[语义表示边界](#semantic-representation)。

<a id="interaction-and-repair"></a>

## 4. 修复：候选步骤失败之后发生什么？

[Agent 指南](Litex智能体指南.md)给出一个小型 Session 示例。在没有项目配置的目录启动，下面省略了部分失败输出：

```text
$ litex -lang en -strict -session -e 'have a R = 2'
litex> a = 3
{"run_result": "failure", ..., "session_terminated": false, "termination": null}
litex> a + 1 = 3
success
```

失败的等式不会删除声明或 `a = 2`。下一条语句仍能使用已接受的上下文；换一个进程则需要加载或重放这些上下文。事务单位是一条语句，多条粘贴的语句可以分别提交。硬错误或替换已提交声明可能需要重启。

检查还会返回该步骤的数学效果。对于 `1 + 1 = 2`，普通语句结果包含：

```json
{
  "statement_result": "accepted",
  "statement": "(1 + 1) = 2",
  "proof_method": {
    "type": "by_closed_calculation",
    "rule_name": "Closed calculation",
    "message": "Exact evaluation of closed expressions without proof search"
  },
  "stores": ["(1 + 1) = 2"],
  "infers": []
}
```

`proof_method` 标明检查路线，`stores` 和 `infers` 描述发布的事实。失败反馈区分阶段，并在证据保留时给出相关义务：`1 / x` 可能因为尚未建立 `x != 0` 而失败。没有找到证明，不等于已经证明该事实为假。[CLI 参考](Litex命令行参考.md#json-output-contract)规定具体输出。

这为人和智能体提供了具体的“提出—检查—修正”循环。[Python Session 示例](../examples/agent_session_demo/README.md)演示了一次拒绝后继续进行依赖推理；它是确定性的交互示例，还不是 AI 证明成功率实验。

Lean 也支持[增量 elaboration](https://lean-lang.org/doc/reference/latest/releases/v4.9.0/)、证明状态查看和 [`grind`](https://lean-lang.org/doc/reference/latest/The--grind--tactic) 等自动化。实际比较应让两边使用正常交互工具，记录诊断准确性、重复处理的已接受工作、修复轮数、总耗时与 token，以及修复后的结果是否仍回答原问题。只统计通过率，可能掩盖目标被改动或前提被添加。

<a id="1-direct-facts-short-estimates-and-typed-domains"></a>
<a id="1-直接事实短估计与带类型定义域"></a>
<a id="2-scalar-multiplication-preserves-convergence"></a>
<a id="2-标量乘法保持收敛"></a>
<a id="ai-lowers-generation-cost-not-automatically-understanding-cost"></a>
<a id="keep-the-mathematical-estimate-visible"></a>
<a id="保持数学估计可见"></a>
<a id="understanding-and-reuse"></a>

## 5. 理解与复用：下一位读者能拿成果做什么？

当另一个人能够理解条件，并把结果用于下一段论证时，检查成果才成为可用的知识。Litex 源码保留数学选择，检查记录提供另一层依据说明；这种组织是否帮助新读者，需要实际测量。

### 使用条件跟随数学构造

考虑 `x != 1` 上的 `f(x) = (x+1)/(x-1)`。要证明 `f(f(x)) = x`，必须先建立 `f(x) != 1`，使第二次调用合法。维护中的 [Litex 源码](../lean/examples/real_mobius_involution/statement.lit)如下：

```litex
forall x R:
    x!=1
    =>:
        x-1!=0

have fn mobius(x R:x!=1) R=(x+1)/(x-1)

forall x R:
    x!=0
    =>:
        2/x!=0

thm mobius_preserves_domain:
    ? forall x R:
        x!=1
        =>:
            mobius(x)!=1
    mobius(x)=(x+1)/(x-1)
    mobius(x)-1=2/(x-1)
    2/(x-1)!=0

thm mobius_involution:
    ? forall x R:
        x!=1
        =>:
            mobius(mobius(x))=x
    mobius(x)!=1
    mobius(x)-1!=0
    mobius(x)=(x+1)/(x-1)
    ((x+1)/(x-1))-1!=0
    mobius(mobius(x))=(mobius(x)+1)/(mobius(x)-1)=((x+1)/(x-1)+1)/((x+1)/(x-1)-1)=x
```

可复用结果 `mobius_preserves_domain` 提供 `mobius_involution` 随后消费的条件。定义、保持定义域与继续使用连接成一段数学发展。可以让读者指出被排除的点、解释第二次调用，或继续应用这个映射。

维护中的[原生 Lean 对照](../showcases/litex_to_lean_adapter/DirectLean.lean)也能简洁地证明两项性质：

```lean
import Mathlib

noncomputable def mobius (x : ℝ) : ℝ := (x + 1) / (x - 1)

theorem mobiusInvolution (x : ℝ) (hx : x ≠ 1) :
    mobius x ≠ 1 ∧ mobius (mobius x) = x := by
  unfold mobius
  constructor
  · intro h
    field_simp [sub_ne_zero.mpr hx] at h
    linarith
  · field_simp [sub_ne_zero.mpr hx]
    ring
```

[互操作 showcase](../showcases/litex_to_lean_adapter/README.md)继续展示受支持的 Litex 输出怎样经过 Adapter 变成普通 Lean 定理。这条交接路线有实际的表示转换与维护成本；它展示互操作能力，尚不能据此得出证明更短或编译覆盖完整的结论。

### 分析学中可见的数学选择

数列收敛在数乘下保持时，关键选择是一个更小的容差。[完整例子](#convergence-example)中，Litex 选取 `epsilon / (|c| + 1)`，取得截断点，再写出估计。分母始终为正，包含 `c = 0` 的情形。保留的 Lean 证明选择 `epsilon / |c|` 并单独处理零；Lean 同样能采用统一论证，不能把证明路线的差异归因于语言。

阅读比较可以要求他人恢复这个选择、解释分母为什么合法，并修改估计。生成证明与理解证明是两个任务；模型能生成源码，不代表已经测量了另一位读者的理解。

### 从单条结果到一段数学发展

[数学主题集合](../showcases/math_concepts_in_litex/README.md)提供了有边界的连续发展，包括[平方函数的导数](../showcases/math_concepts_in_litex/7_calculus/README.md)和[坐标几何库](../showcases/math_concepts_in_litex/15_coordinate_geometry_case_study/README.md)。可以据此比较定义概念、建立引理、使用构造、修改条件和向另一位作者交接的全过程。各模块注明日期的 Litex 检查，不同时确立所有 Lean 对照文件或整个数学学科的覆盖。

分别测量知识建设与知识消费：先建立一个接口需要多少投入，再由新使用者调用它需要多少投入。库的建设、检查器改动和 Adapter 工作均应记录，不能作为免费前提。这有助于区分可普遍使用的语言机制，以及依赖逐题实现支持的示例集合。

<a id="4-witnesses-contradiction-and-counterexamples"></a>
<a id="4-见证反证与反例"></a>
<a id="a-concrete-witness"></a>
<a id="具体见证"></a>
<a id="checking-performance"></a>

## 6. 性能：工作流能负担多少次检查？

每个候选数学步骤都能收到反馈时，检查延迟会直接影响工作方式。数量级的速度差异可能改变交互试探、智能体搜索或交互教材逐步检查的成本。这些工作流效果仍需检验；检查器更快本身尚不能确立最终数学任务的完成收益。

<a id="9-local-runtime-spot-checks"></a>

### 2026-10-21 的本地运行时观察

已有的 Apple Silicon 本地抽查记录如下。Litex 使用已构建的 `target/release/litex -f`；Lean 在 `showcases/litex_to_lean_adapter` 中使用 `lake env lean`，已有 Mathlib olean 缓存。Litex 列是多次运行的中位数，Lean 列是第二次较暖运行。本表保留当时的观察，本文新增的证明写法没有重新计时。

| 场景 | Litex（中位） | Lean（第 2 次较暖） | 约计比值 |
| --- | --- | --- | --- |
| 短算术 / `x = 2` ⇒ `x + 1 = 3`，`x^2 = 4` | ~6 ms | ~7 s | ~1000× |
| 二元一次方程计算链 | ~16 ms | ~30 s | ~2000× |
| 集合：交保持包含 | ~4 ms | ~3.4 s | ~800× |
| 大数见证 `a^4 + b^4 + c^4 = d^4`（95800…） | ~5 ms | ~16–21 s（`norm_num` / `native_decide`） | ~3000×+ |
| 对照：Lean 无 Mathlib 的 `1 + 1 = 2` | — | ~2.3 s（`lake env lean` 启动） | 无配对比值 |

这些命令行运行中的数量级差距，是值得突出的一项观察。Lean 时间包含启动和加载，对短证明可能占主导；这组观察没有分离纯证明搜索，也没有覆盖编辑器中已经加载依赖的增量检查。Litex 直接进行精确闭式计算和上下文检查；Lean 的 `norm_num` 等 tactic 构造证明项，再由内核检查。两者采用不同的检查架构和信任边界。

### 给定见证：检查成本与发现成本分别计量

下面这组数是欧拉幂和猜想在四次幂上的反例：三个正四次幂等于另一个正四次幂，

\[
95800^4 + 217519^4 + 414560^4 = 422481^4.
\]

Litex 陈述给定的见证，检查其成员关系与方程：

```litex
witness exist a, b, c, d N+ st {a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4} from 95800, 217519, 414560, 422481
```

Lean 证明提供同样的数：

```lean
import Mathlib

example : ∃ a b c d : ℕ,
    a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧
    a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4 := by
  refine ⟨95800, 217519, 414560, 422481, ?_⟩
  norm_num
```

计时行衡量给定见证后的验证，不衡量怎样发现这些数，也不重建历史反证过程。

### 怎样测出速度对工作流的影响

| 测量 | 回答什么问题 |
| --- | --- |
| 新进程，包含依赖 | 检查独立候选或文件的成本。 |
| 常驻交互进程中的新语句 | 反复“提出—检查—修正”的延迟。 |
| 增长的上下文和依赖深度 | 查找、加载和重新检查能否持续负担。 |
| 固定预算下的完整任务 | 检查时间怎样与生成、搜索、修复和完成结合。 |
| 要求独立检查的任务 | 源码检查、证明生成、Adapter 和后端复核的总成本。 |

现有表格只覆盖第一行的一小组本地样本，不能推出 AI 成功率或吞吐量也提高一千倍。正式计时应冻结源码与工具，保留原始命令和输入，统一重复方式，报告波动与内存，并保留失败案例。

<a id="a-research-hypothesis-that-can-be-tested"></a>
<a id="reading-the-comparison-fairly"></a>
<a id="公平阅读对比"></a>
<a id="可检验的研究假设"></a>
<a id="evaluating-the-comparison"></a>

## 7. 评价：把设计差异连接到数学工作

这些接口差异提出一项假设：以事实为中心的源码、显式条件、局部反馈和低检查延迟，可能降低构造和使用可检查数学知识的成本。示例与本地计时尚未确立这个组合效果；本页没有报告受控的作者效率、模型成功率或人类阅读实验结果。

| 维度 | 建议测量的结果 |
| --- | --- |
| 构造 | 共同预算下的正确完成率；作者时间、定理查找、辅助源码、模型与工具调用。 |
| 原意保持 | 定义域、量词、前提和结论是否符合独立固定的数学任务。 |
| 知识积累 | 同一对象或结果进入不同上下文所需的工作，包含转换和辅助证据。 |
| 修复 | 保持原陈述的修复时间与轮数；对正确源码造成的不必要改动。 |
| 理解与复用 | 新读者识别条件、解释路线、发现错误和完成后续任务的准确率与耗时。 |
| 检查容量 | 多种依赖规模下的延迟、总时间、内存，以及每单位总预算的正确完成数。 |

采用两种分别报告的库条件：对齐数学背景知识，用于研究接口；使用各系统现成生态，用于衡量当前实际成本。[素数例子](#prime-example)说明了区别：Litex 证明把背景事实列作前提，Lean 证明调用 Mathlib 中已经证明的库结果。不能把库条件的差异直接归因于语言设计。

第一轮可以集中在三个案例：方程计算链测构造与延迟，Möbius 变换测条件与修复，平方函数导数测“定义—引理—应用”的连续发展。测试前固定等价的数学要求，允许 Lean 使用正常自动化和增量工具。失败与不支持的任务保留在结果中，环境准备和库建设成本与反复使用成本分别报告。

小内核、证明项、依赖类型、库规模和社区经验，分别回答可信性、表达能力与生态成熟度的重要问题。应说明这些性质影响哪项任务；同样，让 Litex 的直接事实和快速检查接受数学活动的检验。这样，比较始终围绕实际结果展开，而不会停留在功能清单或最短代码竞赛。

<a id="7-a-technical-boundary-facts-are-not-first-class-objects"></a>
<a id="7-技术边界事实不是一等对象"></a>
<a id="a-semantic-difference-behind-the-syntax-eq-and-same"></a>
<a id="syntax-semantics-and-foundations"></a>
<a id="从语法语义对象与数学基础开始"></a>
<a id="数学基础起点的差异也影响表达"></a>
<a id="语法背后的语义差异eq-与-same"></a>
<a id="trust-and-scope"></a>

## 8. 数学基础、支持范围与信任

Litex 仍是 beta 阶段的实验项目。它的集合导向源码模型与 Lean 的依赖类型论，以不同方式组织对象、命题与证明。上文 Mathlib 的运算约定属于库选择，并非依赖类型论强迫的结果。Litex 区分对象与事实；Lean 还支持一般的命题和证明编程。比较应覆盖任务实际需要的数学与接口，也列出不支持的形式及扩展所需工作。

仅用 Litex 检查时，Rust verifier 及 builtin、infer rules 仍属于需要信任的实现。`-strict` 排除源码中的 `trust` 和用户公理，不独立证明验证器正确。源码例子、规则审计和独立检查提供不同层次的证据，应分别报告。

当前 `-lean -f` 编译器重放受支持的带类型执行证据。[编译器指南](Litex到Lean编译器指南.md)说明其覆盖、显式语义参数、模型和表示桥接。经过审查的 Adapter 所提供的普通 Lean 定理，比尚未实例化语义假设的生成定理，提供更完整的集成证据；这些均不确立全部 Litex 的完整 Lean 解释。

<a id="semantic-representation"></a>

### 源码身份与后端表示

成员关系例子保留同一个源码对象，让关于它的事实增加。受支持的 Lean 重放中，`Litex.Same` 记录认证表示之间的语义相等，`Litex.In` 记录成员关系。生成的 Lean 仍有类型；恢复原生 Lean 相等需要对应的忠实表示桥接，异质语义相等不是到 Lean `Eq` 的全局转换。[语义接口](../lean/Litex.lean)与编译指南维护这些具体契约。

两种语言都需要分别检查证明有效性与原意对应。[Lean 证明验证指南](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)也区分这两个问题。性能或使用成本的结论，应说明任务要求的检查保证与数学假设。

<a id="contraposition-by-contradiction"></a>
<a id="通过反证证明逆否"></a>
<a id="supporting-examples"></a>

## 更多完整例子

下面保留的例子把比较扩展到开头的计算之外。每个例子承担一个具体任务：可见的容差选择、不同的背景库条件，或显式反例。

<a id="convergence-example"></a>

### 数乘保持收敛

两份证明都在更小的正容差处取得尾部界，再复用截断点。Lean 证明采用 `epsilon / |c|`，单独处理 `c = 0`：

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

Litex 证明采用 `epsilon / (|c| + 1)`：

```litex
prop is_eventually_close(s fn(n N) R, a R, epsilon R+, N0 N):
    forall n N:
        n >= N0
        =>:
            |s(n) - a| < epsilon

prop converges_to(s fn(n N) R, a R):
    forall epsilon R+:
        exist N0 N st {$is_eventually_close(s, a, epsilon, N0)}

thm converges_to_mul_const:
    ? forall s, scaled fn(n N) R, a, c R:
        $converges_to(s, a)
        forall n N:
            scaled(n) = c * s(n)
        =>:
            $converges_to(scaled, c * a)
    claim:
        ? forall epsilon R+:
            exist N0 N st {$is_eventually_close(scaled, c * a, epsilon, N0)}
        |c| >= 0
        |c| + 1 > 0
        have scale R+ = |c| + 1
        epsilon / scale > 0
        epsilon / scale $in R+
        |c| <= scale
        obtain N0 from exist K N st {$is_eventually_close(s, a, epsilon / scale, K)}
        witness exist K N st {$is_eventually_close(scaled, c * a, epsilon, K)} from N0:
            claim:
                ? forall n N:
                    n >= N0
                    =>:
                        |scaled(n) - c * a| < epsilon
                scaled(n) = c * s(n)
                |s(n) - a| < epsilon / scale
                |s(n) - a| >= 0
                scaled(n) - c * a = c * s(n) - c * a = c * (s(n) - a)
                |scaled(n) - c * a| = |c * (s(n) - a)| = |c| * |s(n) - a|
                |c| * |s(n) - a| <= scale * |s(n) - a|
                scale * |s(n) - a| < scale * (epsilon / scale) = epsilon
                |scaled(n) - c * a| = |c| * |s(n) - a| <= scale * |s(n) - a| < epsilon
            by def $is_eventually_close(scaled, c * a, epsilon, N0)
    by def $converges_to(scaled, c * a)
```

见证、正性事实与不等式链，让读者能检查论证中的数学选择，常规连接由上下文支持。这可用于阅读与修改任务；若要分离接口效果，应在两边提供同一条数学路线。

<a id="6-case-study-infinitely-many-primes"></a>
<a id="6-案例无穷多个素数"></a>
<a id="prime-example"></a>

### 无穷多个素数：让背景知识保持可见

欧几里得论证构造阶乘加一，取得一个素因子，再证明它大于原来的界。Litex 例子把三项一般背景结果列作前提：乘积的整除性质、素因子的存在性，以及乘积下界。

```litex
have fn factorial_factor(x N+) N+ = x

# `$prime(a)` is native. Its symbolic contract is `2 <= a` together with
# `a % b != 0` for every `b` in `range(2, a)`.

claim:
    ? forall a N+:
        forall n, d N+:
            d <= n
            =>:
                product(1, n, factorial_factor) % d = 0
        forall n N+:
            2 <= n
            =>:
                exist k N+ st {$prime(k), n % k = 0}
        forall n N+:
            n <= product(1, n, factorial_factor)
        2 <= a
        =>:
            exist k N+ st {k > a, $prime(k)}
    product(1, a, factorial_factor) $in N+
    product(1, a, factorial_factor) $in R
    2 <= a <= product(1, a, factorial_factor) <= product(1, a, factorial_factor) + 1
    product(1, a, factorial_factor) + 1 $in N+
    2 <= product(1, a, factorial_factor) + 1
    obtain k from exist k N+ st {$prime(k), (product(1, a, factorial_factor) + 1) % k = 0}
    by cases:
        ? k > a
        case k <= a:
            product(1, a, factorial_factor) % k = 0
            2 <= k
            (product(1, a, factorial_factor) + 1) % k = (product(1, a, factorial_factor) % k + 1 % k) % k
            1 % k = 1
            (0 + 1) % k = 1 % k = 1
            (product(1, a, factorial_factor) + 1) % k = (product(1, a, factorial_factor) % k + 1 % k) % k = (0 + 1) % k = 1
            (product(1, a, factorial_factor) + 1) % k != 0
            impossible (product(1, a, factorial_factor) + 1) % k = 0
        case k > a:
            k > a
    witness exist prime_larger N+ st {prime_larger > a, $prime(prime_larger)} from k
```

Lean 例子调用 Mathlib 的阶乘与素因子定理：

```lean
import Mathlib

example (N : ℕ) : ∃ p ≥ N, Nat.Prime p := by
  have hN0 : 0 < Nat.factorial N := Nat.factorial_pos N
  have hN_ne_one : Nat.factorial N + 1 ≠ 1 := by omega
  obtain ⟨p, hp, hpN⟩ :
      ∃ p : ℕ, Nat.Prime p ∧ p ∣ Nat.factorial N + 1 :=
    Nat.exists_prime_and_dvd hN_ne_one
  use p
  constructor
  · by_contra hlt
    have hp_le_N : p ≤ N := by omega
    have hp_dvd_factorial : p ∣ Nat.factorial N :=
      (Nat.Prime.dvd_factorial hp).2 hp_le_N
    have hp_dvd_one : p ∣ 1 := by
      have hp_dvd_sum : p ∣ (Nat.factorial N + 1) - Nat.factorial N :=
        Nat.dvd_sub hpN hp_dvd_factorial
      simpa using hp_dvd_sum
    exact Nat.Prime.not_dvd_one hp hp_dvd_one
  · exact hp
```

Litex claim 检查列明前提下的条件论证，没有在此建立这些背景结果。两份例子展示了同一欧几里得思想的两条路线，但其假设没有对齐，不能直接作为语言效率 benchmark。完整比较需要计入建立等价背景知识的工作。

<a id="a-set-counterexample"></a>
<a id="集合反例"></a>
<a id="set-counterexample"></a>

### 别人可以恢复的反例

自然数 `2` 区分偶数集合与 `4` 的倍数集合：

```litex
have multiples_of_four power_set(N) = {a N: a % 4 = 0}
have multiples_of_two power_set(N) = {a N: a % 2 = 0}
by contra:
    ? multiples_of_four != multiples_of_two
    2 $in multiples_of_two
    2 $in multiples_of_four
    impossible 2 % 4 = 0
```

```lean
import Mathlib

example : ({a : ℕ | a % 4 = 0} : Set ℕ) ≠
    {a : ℕ | a % 2 = 0} := by
  intro h
  have h2 : (2 : ℕ) ∈ ({a : ℕ | a % 2 = 0} : Set ℕ) := by
    norm_num
  have h4 : (2 : ℕ) ∈ ({a : ℕ | a % 4 = 0} : Set ℕ) := by
    rw [h]
    exact h2
  norm_num at h4
```

两份源码都展示关键元素与矛盾的成员关系。审阅任务可以要求读者识别并复用这个反例；token 数量不能代替读者是否成功。

<a id="further-reading"></a>

## 延伸阅读

- [Litex 蓝图](https://litexlang.com/doc/Litex中文蓝图)：完整语言设计论证与群单位元例子。
- [手册](Litex手册.md)和 [CLI 参考](Litex命令行参考.md)：支持的语言、信任与交互契约。
- [Agent 指南](Litex智能体指南.md)：持续 Session 与重启边界。
- [数学主题模块](../showcases/math_concepts_in_litex/README.md)：定义、构造与后续使用。
- [Litex 到 Lean 编译器指南](Litex到Lean编译器指南.md)和[互操作 showcase](../showcases/litex_to_lean_adapter/README.md)：受支持的重放与普通 Lean 接口。
