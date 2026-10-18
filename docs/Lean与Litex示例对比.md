<a id="representative-leanlitex-example-comparisons"></a>

# Lean–Litex 代表性示例对比

由沈嘉辰创建和维护。

在浏览器中尝试示例：
https://litexlang.com/doc/Representative_Lean_Litex_Example_Comparisons

Markdown 源码：
https://github.com/litexlang/golitex/blob/main/docs/Representative_Lean_Litex_Example_Comparisons.md

> **Litex 是一个仍处于 beta 阶段的实验性业余项目，使用中可能遇到不完善之处。**

本页提供少量代表性示例，而不是完整的语言比较。Lean 与 Litex 都使数学可以由机器检查，但默认接口有所不同：

- Lean 提供依赖类型论、证明项、tactic、Mathlib、成熟工具和庞大社区。
- Litex 提供以事实为导向、以集合论为基础的表层接口；用户通常写下下一条数学事实，由检查器搜索支持它的依据。

这些是侧重点差异，不是绝对能力边界。Lean 能支持简洁自动化与前向推理；Litex 也有显式目标、命名定理、分情形、归纳和其他结构化证明形式。以下 Lean 证明有意保留足够的显式步骤，以便展示比较，不是在声称它们是最短的 Lean 证明。

未跳过的 Litex 块都是自足的，由仓库文档测试检查。明确标为迁移示例的块保留当前内核尚未解决的边界，不是通过的示例。Lean 块直接使用 Mathlib，不依赖 *Mathematics in Lean* 教材包。两边的语法与自动化都可能继续演进。

更完整的设计论证见 [Litex 蓝图](https://litexlang.com/doc/Litex中文蓝图)。语言细节见[手册](Litex手册.md)和 [CLI 参考](Litex命令行参考.md)。当前预览模式 `-lean -f` 重放有限的带类型结果集合。[语义接口](../lean/Litex.lean)与[生成示例对](../lean/examples/)展示已支持的路线。维护中的源码与生成结果讲解见[编译器指南](Litex到Lean编译器指南.md)。下文语义讨论中的历史输出器与设计目标不代表当前编译器覆盖范围。

完整的 `Group` 对比放在蓝图中，不在此重复。本页集中展示能增加独立证据的示例。示例之后，[第 8 节](#8-a-design-perspective-what-the-author-states-what-the-checker-reconstructs)将它们连接到一个形式化语言设计提案：哪些决定属于数学源码，哪些工作应由检查器重建。

<a id="syntax-semantics-and-foundations"></a>

## 从语法、语义、对象与数学基础开始

Litex 的目标，是成为形式化语言里的 Python，让学生、工程师与研究者能把形式化数学用进自己的工作。减少输入符号是其中一部分；另一部分，是让熟悉的数学想法、定义域条件与论证顺序直接对应源码。

| 角度 | Lean / Mathlib | Litex 的源码接口 |
| --- | --- | --- |
| 语法 | 定理具有带类型的陈述与证明项；tactic 和自动化可以构造证明项。 | 直接写下一条事实，由验证器在已接受的上下文中寻找依据。 |
| 运算语义 | 一些熟悉的运算被扩展到了教科书通常不使用的定义域。 | 接受使用某个表达式的事实之前，先建立表达式有定义。 |
| 对象与性质 | 通过类型、转换、子类型与证明参数组织接口。 | 成员关系与条件是对象的事实；带条件的调用直接检查上下文中的这些事实。 |
| 数学基础 | 以依赖类型论组织数学对象、命题与证明。 | 以集合论源码模型，从集合、函数、关系与显式事实出发。 |

### 语法：先写想要成立的事实

Lean 可以简洁地证明一个小算式：

```lean
example : (1 : Nat) + 1 = 2 := by
  rfl
```

对应的 Litex 输入就是事实本身：

```litex
1 + 1 = 2
```

区别在于书写证明的接口，并非这个算式对 Lean 很难。更大的证明仍需要作者选择有意义的中间步骤。[第 1 节](#1-direct-facts-short-estimates-and-typed-domains)用实际证明比较这种工作流。

<a id="ordinary-mathematics"></a>

### 语义：Litex 走“正常数学”的路线

**Litex 希望保留通常教科书中的数学含义与定义域条件。** 除法要求分母非零，实数平方根要求输入非负。接受使用这些表达式的事实之前，验证器必须先建立相应条件。这里的“正常数学”落实为一个具体目标：作者沿用自己想表达的数学含义，由语言检查其使用条件。

下面三个例子涉及运算定义。Mathlib 的扩展是库的主动约定，并非依赖类型论必然要求如此；Lean 也能表达受限的定义域。

#### 除以零

Mathlib 的标准实数除法满足：

```lean
import Mathlib

example : (1 : ℝ) / 0 = 0 := by
  simp
```

Litex 将非零条件放在函数定义域中：

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

Litex 在良定义性检查处拒绝 `1 / 0 = 0`：所需条件 `0 != 0` 无法成立，不会给它一个默认值。Mathlib 的对应约定见 [`div_zero`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/GroupWithZero/Basic.html#div_zero)。

区别在于非零条件在哪里被检查。Mathlib 在 `x / x = 1` 等定理中要求这个前提；Litex 在接受含有该除法的事实之前就检查它，连 `1 / 0 = 1 / 0` 也会被拒绝。[Lean 的除零 FAQ](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/)解释了 Mathlib 的选择，以及为何这种扩展不允许在零分母处错误地约分。

#### 自然数减法

Lean 的自然数减法在零处截断：

```lean
example : (1 : Nat) - 2 = 0 := by
  decide
```

Litex 不会因为两个输入都是自然数，就把减法改成截断减法：

```litex
1 - 2 = -1
1 - 2 $in Z
```

结果是整数。Lean 也提供通常的整数减法；这里的区别是类型选择了哪种运算。参见 [`Nat.sub`](https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/#Nat.sub)。

#### 负数输入的实数平方根函数

Mathlib 将 `Real.sqrt` 扩展为对负数返回零：

```lean
import Mathlib

example : Real.sqrt (-1) = 0 := by
  exact Real.sqrt_eq_zero_of_nonpos (by norm_num)
```

Litex 的实数平方根运算要求输入非负：

```litex
have fn real_root(x R: x >= 0) R = sqrt(x)
real_root(4) = 2
```

`sqrt(-1) = 0` 在良定义性检查处被拒绝，那里要求 `0 <= -1`。这体现的是运算定义域约定的区别。Mathlib 的值并不表示零的平方等于负一；通常的平方根恒等式仍保留定义域前提。参见 [`Real.sqrt_eq_zero_of_nonpos`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Real/Sqrt.html#Real.sqrt_eq_zero_of_nonpos)。

### 对象：知道一个性质，与打包一个子类型

假设已有实数 `x`，也已证明 `0 <= x`。接受非负实数子类型的 Lean 接口，把值与证明打包在一起：

```lean
import Mathlib

def nonnegativeInput (x : {y : ℝ // 0 ≤ y}) : ℝ := x.val

example (x : ℝ) (h : 0 ≤ x) : nonnegativeInput ⟨x, h⟩ = x := by
  rfl
```

对应的 Litex 接口将条件保留为参数的事实：

```litex
have fn nonnegative_input(x R: x >= 0) R = x

forall x R:
    x >= 0
    =>:
        nonnegative_input(x) = x
```

Litex 使用同一个 `x` 作为参数时检查已知条件，源码不需要为这个条件把值与证明打包。条件义务仍在：`nonnegative_input(-1) = -1` 会在良定义性检查处被拒绝。Lean 也能改用独立的证明参数，自动化还可以补全部分打包工作；这里比较的是接口，而非声称 Lean 不能表达带条件的函数。参见 [Lean 子类型](https://lean-lang.org/doc/reference/latest/Basic-Types/Subtypes/)。

数值表示也体现了类似区别。实数 `1` 与复数 `1` 属于不同的 Lean 类型，但通过标准嵌入后相等：

```lean
import Mathlib

example : ((1 : ℝ) : ℂ) = (1 : ℂ) := by
  simp
```

在 Litex 中，同一个源码对象可以逐步积累成员事实：

```litex
have a N = 1
a $in Z
a $in R
a $in C
```

这不是说 Lean 中的实数一与复数一在数学上不相等，也不是说生成的 Lean 没有类型，而是展示身份、成员关系与表示的源码接口有所不同。后面的 `Eq`/`Same` 章节进一步讨论桥接；Mathlib 的数值嵌入见 [`Complex.ofReal_one`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Basic/Complex/Basic.html#Complex.ofReal_one)。

### 数学基础：起点的差异，也影响表达

不同的基础体系可以各自在内部保持一致，同时采用不同方式组织对象、相等与证明。Lean 使用[依赖类型论](https://lean-lang.org/theorem_proving_in_lean4/Dependent-Type-Theory/)，数学论述则常以集合为出发点。这些描述不构成任何体系绝对一致性的证明，日常数学也没有唯一的形式化表述。上面的除零和平方根扩展属于库定义，并非 Lean 公理强制的结果。

Litex 探索的是：熟悉的源码对象、定义域条件与事实导向证明写法，能否降低构造与理解可检查数学的成本。这是需要跨任务检验的设计目标；这些示例证明的是各自具体行为，不代表普遍覆盖、更高正确性或完整的 Lean 编译能力。

---


<a id="a-semantic-difference-behind-the-syntax-eq-and-same"></a>

## 语法背后的语义差异：`Eq` 与 `Same`

一项关键区别不能从表层证明长度看出来。Lean 的命题相等是同类型的：

```lean
Eq : {α : Sort u} → α → α → Prop
```

因此 `x = y` 要求两项属于同一个 Lean 类型，表示它们是该载体中的同一个值，并支持代换、改写与依赖传递。

保留的 Lean ABI 使用 `Litex.Same` 表示 Litex 源码相等：这是跨表示的异质语义相等。例如：

```lean
n       : ℕ
(n : ℤ) : ℤ
(n : ℂ) : ℂ
```

它们不能成为同一个 Lean `Eq` 的端点，因为载体不同。但借助经过审查的数值表示桥接，可以证明它们表示同一个 Litex 数学值。`Same` 也不只是 Lean 的 `HEq`：`HEq` 属于依赖类型论对项身份的描述，而 `Same` 有意记录经过认可的表示之间的数学同一性。

准确的设计描述是**以成员关系为导向、独立于表示的语义**。这不表示生成的 Lean 没有类型，而是 Litex 不将一个对象的完整数学分类永久编码在唯一的源码类型中。`x $in N`、`x $in Z` 和 `x $in R` 等事实可以不断积累，无需重新指定类型或替换 `x`。`Litex.In x S` 记录：`x` 所表示的语义值，在 `S` 的精确载体中有一个 `Same` 代表元。

一个有用的概念图景是：

```text
(α, x)      (β, y)      (γ, z)
    \          |          /
          Litex.Same
               |
    one Litex mathematical value
```

这类似于取宿主表示的等价类。实际 Lean 包装不构造商，而是保留具体代表元与证明证据，让内核可以检查每个桥接。

全局关系有意保持不对称：

```text
Lean Eq ⊆ Litex.Same
```

Lean 相等始终能通过 `Same.ofEq` 导出 `Same`。一般而言这是严格包含：即使两个端点具有相同 Lean 类型，`Same` 也不自动导出 `Eq`。例如两个 `Litex.Set` 值可以表示相同外延，却打包不同的精确载体。因此恢复原生 Lean 相等，要求两个端点都经由经过审查的忠实/单射观察映射到规范载体。`Same.complexNativeEq` 因而可以把 `x y : ℂ` 上的 `Same x y` 转为 `x = y`，但不存在从异质 `Same` 到 Lean `Eq` 的全局转换。

这是默认语义接口的差异，不是在声称 Lean 不能表达集合导向数学或异质关系。Litex 包装本身就在 Lean 中定义并检查。设计选择是让成员关系与跨表示身份成为显式源码语义义务，只在经审计的特化边界恢复原生 Lean 相等。

---

<a id="1-direct-facts-short-estimates-and-typed-domains"></a>

## 1. 直接事实、短估计与带类型定义域

<a id="direct-local-consequences"></a>

### 直接的局部推论

假设已知一个实数等于 `2`。Litex 把该事实放进局部上下文，直接陈述所需推论：

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4
```

显式 Lean 证明可以命名假设，并指示两次改写：

```lean
import Mathlib.Tactic

example (x : ℝ) (h : x = 2) : x + 1 = 3 ∧ x ^ 2 = 4 := by
  have h_add : x + 1 = 3 := by
    rw [h]
    norm_num
  have h_square : x ^ 2 = 4 := by
    rw [h]
    norm_num
  exact ⟨h_add, h_square⟩
```

数学内容相同。Litex 源码突出两个结果，由检查器提供代换与算术支持。Lean 源码突出构造合取的路线，最终由内核检查得到的证明项。

<a id="ai-lowers-generation-cost-not-automatically-understanding-cost"></a>

<a id="keep-the-mathematical-estimate-visible"></a>

### 保持数学估计可见

假设 `0 < epsilon <= 1`、`|x| < epsilon`、`|y| < epsilon`。`|x * y| < epsilon` 成立的原因是简短估计：

\[
|xy| = |x||y| < \varepsilon^2 \leq \varepsilon.
\]

显式 Lean 计算如下：

```lean
import Mathlib

example (x y epsilon : ℝ)
    (epsilon_pos : 0 < epsilon)
    (epsilon_le_one : epsilon ≤ 1)
    (hx : |x| < epsilon)
    (hy : |y| < epsilon) :
    |x * y| < epsilon := by
  rw [abs_mul]
  calc
    |x| * |y| < epsilon * epsilon := by
      nlinarith [abs_nonneg x, abs_nonneg y]
    _ ≤ epsilon * 1 := by
      exact mul_le_mul_of_nonneg_left epsilon_le_one (le_of_lt epsilon_pos)
    _ = epsilon := mul_one epsilon
```

对应的 Litex 示例在上下文中保留一个一般的乘积单调性前提，将持久的论证写成容易辨认的估计：

```litex
claim:
    ? forall x, y, epsilon R:
        forall a, b, c, d R:
            0 <= a < c
            0 <= b < d
            =>:
                a * b < c * d
        0 < epsilon
        epsilon <= 1
        |x| < epsilon
        |y| < epsilon
        =>:
            |x * y| < epsilon
    0 <= |x| < epsilon
    0 <= |y| < epsilon
    |x * y| = |x| * |y| < epsilon * epsilon <= epsilon * 1 = epsilon
```

AI 可以低成本生成任一种证明。接口问题在于，之后哪些内容仍便于数学家查看和编辑。Litex 希望把数学主线留在源码中，同时通过输出记录每步来自已知事实、全称实例、定义、内置规则、命名定理还是显式假设。

<a id="domains-carried-by-mathematical-objects"></a>

### 数学对象携带的定义域

Litex 能将条件直接放进对象的定义域，再在对象作为函数参数时使用该条件：

```litex
forall x {y R: y > 0}:
    x > 0

have fn positive_successor(x R: x > 0) R = x + 1

positive_successor(1) = 2
```

一种自然的 Lean 表示用子类型打包实数值与证明：

```lean
import Mathlib

example (x : {y : ℝ // y > 0}) : (x : ℝ) > 0 := by
  exact x.property

def positiveSuccessor (x : {y : ℝ // y > 0}) : ℝ := x.val + 1

example : positiveSuccessor ⟨1, by norm_num⟩ = 2 := by
  norm_num [positiveSuccessor]
```

Litex 将条件保留在数学家通常书写定义域的位置。Lean 子类型在类型论对象语言内部精确表达该依赖。两者都不消除参数满足条件的义务；义务呈现在不同表层。

---

<a id="2-scalar-multiplication-preserves-convergence"></a>

## 2. 标量乘法保持收敛

假设实数序列 `s` 收敛到 `a`。每项乘以实常数 `c`，所得序列应收敛到 `c * a`。

以下 Lean 证明使用通常的 epsilon 定义。它按 `c = 0` 分情况；非零时在 `epsilon / |c|` 处应用收敛性，并使用绝对值乘积规律。

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

Litex 证明选择 `epsilon / (|c| + 1)`。由于分母始终为正，一条估计同时覆盖 `c = 0` 和 `c != 0`。

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

两份证明使用同一核心思路：对更小的正容差取得尾部界，复用同一个截断点，并估计缩放后的绝对差。Lean 证明暴露分情况、命名假设、改写和库引理。Litex 证明暴露嵌套收敛事实、见证与不等式链，由检查器提供常规算术与定义折叠。

这不声称 Lean 必须采用这种证明形状，也不声称它不能使用统一的 `|c| + 1` 论证。比较的是组织同一个初等分析证明的两种自然方式。

---

<a id="3-calculation-chains"></a>

## 3. 计算链

Litex 将链视为一条事实语句。二元方程组的中间表达式可以按手写计算的顺序书写：

```litex
forall x, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14
    =>:
        y = 2 * (2 * x + 3 * y) - (4 * x + 5 * y) = 6
        x = ((2 * x + 3 * y) - 3 * y) / 2 = (-4)
```

显式 Lean 证明可以在两个命名子证明中展示相同计算：

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

可见差异不在于能否表达计算链，而在于用户通常指示哪些部分：Litex 要求有意义的中间等式，再搜索支持；这份 Lean 证明命名子结果，并指定构建它们的 tactic 与改写。

---

<a id="4-witnesses-contradiction-and-counterexamples"></a>

## 4. 见证、反证与反例

<a id="a-concrete-witness"></a>

### 具体见证

Litex 将见证值直接放在存在陈述旁边：

```litex
witness exist a, b, c, d N+ st {a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4} from 95800, 217519, 414560, 422481
```

Lean 通过存在量词构造器打包同样的值与剩余义务：

```lean
import Mathlib

example : ∃ a b c d : ℕ,
    a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧
    a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4 := by
  refine ⟨95800, 217519, 414560, 422481, ?_⟩
  norm_num
```

证明义务没有消失：Litex 仍检查给定对象属于 `N+`，并满足代入后的方程。

<a id="contraposition-by-contradiction"></a>

### 通过反证证明逆否

下例使用抽象谓词，因此只讨论逻辑形状：

```litex
abstract_prop p0(x, y)
abstract_prop q0(x, y)

claim:
    ? forall:
        forall a, b R:
            $p0(a, b)
            =>:
                $q0(a, b)
        not $q0(1, 2)
        =>:
            not $p0(1, 2)
    by contra:
        ? not $p0(1, 2)
        impossible $q0(1, 2)
```

```lean
import Mathlib

example (p q : ℝ → ℝ → Prop)
    (h : ∀ a b, p a b → q a b)
    (hnq : ¬ q 1 2) :
    ¬ p 1 2 := by
  intro hp
  exact hnq (h 1 2 hp)
```

Litex 暴露熟悉的动作：“假设否定目标不成立，导出不可能事实。”Lean 把证明表达为从临时假设到矛盾的函数。二者都严谨地表示同一逻辑论证。

<a id="a-set-counterexample"></a>

### 集合反例

证明 `4` 的倍数不是偶自然数时，`2` 是决定性的反例：

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

Litex 证明陈述反例与所得矛盾。Lean 证明命名集合相等与成员关系，用假设的相等改写，再消解错误的模事实。

---

<a id="5-set-theoretic-objects-at-the-surface"></a>

## 5. 表层的集合论对象

比较表层证明之前，必须理解 Litex 的一个区别：

```text
forall x S    means  x $in S
forall A set  means  $is_set(A)
```

这里 `set` 是参数种类，不是全集对象。第二种形式不引入包含全部对象的源码集合。当前语义接口保留一般载体，用 `Litex.Obj` 将值与 WD 证据包装起来。一般集合绑定变量的示意接口如下：

```lean
∀ {αA : Type v} [Litex.Representation M αA]
  (A : Litex.Obj (M := M) αA) (hA : Litex.IsSet A), ...
```

`Litex.In x A` 是关于两个已认证对象的普通命题，不改变 `x` 的宿主类型。一般集合绑定变量与集合构造器仍在首批编译器切片之外。当前实际生成示例覆盖数值事实、R/C 绑定变量和已认证算术对象；早期的精确载体输出器属于历史实现。

嵌套集合、幂集成员关系和子集传递，在 Litex 中都可写成普通数学事实：

```litex
{1, 2} $in {{}, {1, 2}}

{1, 2} $subset {1, 2, 3}
{1, 2} $in power_set({1, 2, 3})

forall A, B set, x A:
    A $subset B
    =>:
        x $in B
```

Lean 表达相同数学，同时显式写出有关的环境类型和集合表示：

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

Litex 表层从集合、对象、成员关系和定义域之间的函数开始。Lean 表层从带类型的项开始，因此示例写 `Set ℕ`、`Set (Set ℕ)` 和一般环境类型 `α`。Lean 的表示更一般，并深度融入依赖类型论；Litex 希望优先呈现集合论读法。

<a id="intersections-preserve-inclusion"></a>

### 交集保持包含关系

以下是 *Mathematics in Lean* 集合章节的显式展开证明。若 `s` 是 `t` 的子集，两者都与同一个 `u` 取交，仍保持包含：

```lean
import Mathlib.Data.Set.Lattice

open Set

example {alpha : Type*} (s t u : Set alpha) (h : s ⊆ t) :
    s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩
```

对应的 Litex 事实就是数学陈述本身：

```litex
forall s, t, u set:
    s $subset t
    =>:
        intersect(s, u) $subset intersect(t, u)
```

数学论证只是：`intersect(s, u)` 的成员同时属于 `s` 和 `u`；子集传递使其属于 `t`，所以属于 `intersect(t, u)`。在 Litex 默认接口中，学习者无需仅为暴露该论证而记住 `subset_def`、`inter_def`、`rw` 或 `simp only [mem_setOf]` 等展开名称和证明命令。这降低初始学习负担，让常规证明留在集合与成员关系层面。

这不声称 Lean 必须使用上述显式脚本；Lean 也支持更短的逐元素证明和更强自动化。这里展示的是默认分工差异。Litex 检查器执行常规展开与成员关系传递，这也把这些规则纳入 Litex 实现与审计范围；Lean 允许作者通过项与 tactic 暴露或控制这些步骤。

载体集合上的结构见 [Litex 蓝图](https://litexlang.com/doc/Litex中文蓝图#group-comparison)中完整的群单位元示例。

---

<a id="6-case-study-infinitely-many-primes"></a>

## 6. 案例：无穷多个素数

两套系统都能以如下形式表达欧几里得论证：

1. 从正界 `a` 开始。
2. 构造 `1 * 2 * ... * a + 1`。
3. 选择该数的素因子 `k`。
4. 若 `k <= a`，则 `k` 整除乘积，而乘积加一模 `k` 的余数为 `1`，矛盾。
5. 因此 `k > a`。

Litex claim 将背景引理放在前提中，以直接的证明主线保留核心论证：

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

Lean 证明可以使用 Mathlib 的阶乘与素因子接口：

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

Litex 示例在 claim 中列出背景假设，再使用 `obtain`、分情况、模运算和见证。Lean 示例引用 Mathlib 的整除定理。两者依赖的背景知识不同。

---

<a id="7-a-technical-boundary-facts-are-not-first-class-objects"></a>

## 7. 技术边界：事实不是一等对象

Lean 命题与证明属于其类型论项语言。Lean 可以对 `P : Prop` 量化，将定理证明作为参数，并递归组合命题。Litex 有意区分数学对象与事实：`prop` 定义创建事实接口，谓词调用是事实，而不是普通对象。

例如，Lean 可以把全称命题直接放进析取：

```lean
example (α : Type) (P : α → Prop) (Q R : Prop) (h : ∀ x, P x) :
    (∀ x, P x) ∨ (Q ∧ R) :=
  Or.inl h
```

Litex 使用更小的规范表层语法。平坦 `and` 包含原子事实；外围 `or` 接受原子、链或完整平坦 `and` 分支；`forall` 不能直接作为这些分支。因此下面的匿名递归形式不是 Litex 语法：

```text
(forall x R: x = x) or (1 = 1 and 2 = 2)
```

闭合的复合事实可以改为取得谓词名称。调用是原子的，可放在外围分支位置。

当前解析器要求 `prop` 参数列表非空。以下闭合零参数谓词保留为预期接口，不是可用语法。当前代码应使用带真实数学参数的谓词。

```litex
prop all_reals_reflexive():
    forall x R:
        x = x

by def $all_reals_reflexive()

$all_reals_reflexive() or 1 = 1 and 2 = 2
```

在该预期接口中，`prop` 定义会使 `$all_reals_reflexive()` 与定义体定义等价；仅定义本身不断言调用。`by def` 行验证定义体并存储原子事实。如果复合子命题有自由数学对象，应把这些对象设为命名谓词的参数。

同样，以下高阶证明编程形式不是 Litex：

```text
forall P Prop:
    # proof body omitted

have h = (x = 2)
some_statement(h)
```

Lean 支持一般的命题与证明项。Litex 区分对象和事实；超出直接可解析形状的复合子命题，需要先定义为命名谓词。

---

<a id="8-a-design-perspective-what-the-author-states-what-the-checker-reconstructs"></a>

## 8. 设计视角：作者陈述什么，检查器重建什么

在这些示例中，作者陈述数学对象和事实，Litex 用局部规则寻找依据。下面说明哪些步骤由作者写出，哪些由检查器完成。

<a id="the-central-inversion-state-the-next-fact-reconstruct-its-grounds"></a>

### 核心倒置：陈述下一条事实，重建其依据

回到第 1 节 `x = 2` 的示例。Litex 作者写下推论 `x + 1 = 3` 与 `x^2 = 4`，验证器寻找代换与算术依据。显式 Lean 证明则写 `rw [h]`、`norm_num` 和 `exact ⟨h_add, h_square⟩` 来构造同样推论的证明。这提出一项设计原则：**写下要验证什么，让验证器确定常规步骤如何得到论证**。

该原则描述源码接口上的分工。Lean 源码也陈述要证明什么。其 tactic 执行和 elaboration 构造核心项，内核按类型论规则检查这些项；内核不会从 tactic 脚本中发现作者预期的定理。[Lean 语言参考](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)明确区分这些阶段。同样，Litex 验证器只在受支持的局部规则内搜索依据，不会发现任意数学论证。作者仍需选择有用的中间事实、见证、估计、情况与归纳论证。

<a id="six-related-changes-of-starting-point"></a>

### 六个相关的起点变化

| 设计问题 | 另一种起点 | Litex 的选择与具体证据 | 后果与边界 |
|---|---|---|---|
| 什么决定对象的数学分类？ | 从宿主类型出发，用强制转换或显式桥接表达表示间移动。 | 从数学对象出发，积累 `x $in N`、`x $in Z`、`x $in R` 等成员事实。开头的 `Eq`/`Same` 讨论解释表示区别。 | 对象知识可以增长而不改变源码身份。生成 Lean 仍有类型；跨表示身份需要已认证语义桥接。 |
| 表达式的使用条件在哪里？ | 将值和条件打包为子类型，或将条件作为证明参数传入。 | 保持数学定义域可见：`have fn positive_successor(x R: x > 0) R = x + 1`，然后 `positive_successor(1) = 2`。第 1 节比较子类型写法。 | 调用要求检查器从上下文建立定义域条件。条件仍是义务；看似合理的方程不能让无定义表达式合法。 |
| 语言的基本类别是什么？ | 像 Lean 一样，用一个依赖项/类型框架表达值、命题与证明。 | 区分对象、事实以及定义或证明它们的语句。第 7 节被拒绝的 `have h = (x = 2)` 说明事实不是普通对象。 | 能形成具有专门事实形状的数学表层，代价是一般证明编程和任意命题嵌套。这是源码语言限制，而不只是记号。 |
| 常规事实如何复用？ | 选择命名引理或证明方法，指示应用。 | 陈述所需事实，按数学内容匹配已有知识。第 5 节在 `s $subset t` 下直接陈述 `intersect(s, u) $subset intersect(t, u)`。 | 名称不必中介每一步。当前检查器按形状和关系索引事实；命名调用仍有价值，匹配受作用域和支持路线限制。 |
| 交互进展的单位是什么？ | 通过把当前目标变换为剩余子目标来推进证明。 | 逐条语句扩展已接受的数学上下文。[Agent 指南](Litex智能体指南.md)中 `a = 3` 失败，已接受的 `a = 2` 仍能在同一个 `-session` 中支持 `a + 1 = 3`。 | 普通失败语句可修复，无需重放已接受工作。边界是语句级的：多语句输入不是一个事务，硬错误可能要求重启。 |
| 检查应留下什么？ | 以已检查定理为主要产物，证明项和工具元数据提供支持。 | 保留带类型的执行结果，描述良定义性、验证依据、引用事实与存储后果。Detailed 输出与当前 Lean 编译器消费这些证据。 | 检查还能产生解释、修复与受支持证明重放的记录。当前结果不是完整可移植证书；编译覆盖和独立检查仍是分开的验收条件。 |

最后四行的实现锚点是[事实类别](../src/ast/fact/fact.rs)、[事实索引与推导](../src/store_fact_and_infer/README.md)、[语句提交边界](../src/execute/exec_stmt.rs)、[输出投影](../src/json_output/README.md)和[结果驱动的 Lean 编译](../src/compile_to_lean/README.md)。当前 [Lean 语义接口](../lean/Litex.lean)在显式语义参数下，通过被表示的含义定义 `Same` 与 `In`；它不确立全部 Litex 对象和规则的完整模型。

<a id="why-the-combination-matters"></a>

### 为什么组合值得研究

成员事实可以支持后续表达式的定义域检查，已接受的等式可以用于代换。同一个 Session 保留这些事实，带类型的结果记录检查依据，用于解释和已支持的 Lean 证明重放。

在 `x = 2` 示例中，作者写出两个推论，检查器执行代换。在收敛示例中，作者给出 `epsilon / (|c| + 1)` 及相应估计。这些是仍需写在源码中的数学选择。

单项思路已有大量先例。[Mizar 手册](https://mizar.uwb.edu.pl/project/mizman.pdf)描述空论证语句、基于引用的 `by` 论证和结构化子证明。[Isabelle/Isar](https://isabelle.in.tum.de/Isar/)提供可读结构化证明与证明方法。[Rocq 的 `auto`](https://rocq-prover.org/doc/master/refman/proofs/automatic-tactics/auto.html)使用有界证明搜索和提示数据库。Lean 也支持前向 `have` 证明、自动化、增量 elaboration 和丰富查看元数据。

<a id="a-research-hypothesis-that-can-be-tested"></a>

### 可检验的研究假设

这种分工能否降低书写、审阅和修复成本，仍待实验回答。实验需要使用等价数学任务、相当的假设与库支持，并记录耗时、修复次数及审阅漏掉的错误。本页提供的是写法示例，尚无这些测量结果。

---

<a id="reading-the-comparison-fairly"></a>

<a id="公平阅读对比"></a>

## 延伸阅读

[手册的 trust 章节](Litex手册.md#trust-and-strict-mode)说明 Litex 结果依赖的检查器、内置规则、导入假设及显式 `trust` 或 `axiom`。

语法、实现与更多示例见：

- [Litex 蓝图](https://litexlang.com/doc/Litex中文蓝图)：设计目标与完整 `Group` 对比；
- [手册](https://litexlang.com/doc/Manual)：语法与证明形式；
- [CLI 参考](Litex命令行参考.md)：当前入口、输出、会话与模块；
- [Lean 语义接口](../lean/Litex.lean)：维护中的重放接口；见[编译器指南](Litex到Lean编译器指南.md)与 [CLI 边界](Litex命令行参考.md#lean-compiler-boundary)。
