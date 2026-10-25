<div align="center">
  <img src="../assets/logo.PNG" alt="Litex logo" width="300">

# Litex

### The Python of Formal Language

**读音：** /ˈliːtɛk/（“里泰克”）。

由沈嘉辰创建和维护。

[官网与在线试用](https://litexlang.com) · [GitHub](https://github.com/litexlang/golitex)
</div>

数学书写本身蕴含逻辑结构，但要让机器检查，往往还需将其翻译成另一种形式化语言。Litex 通过在上下文事实与内置规则中搜索证明依据，让熟悉的数学表达直接接受检查。初步实验报告的德布鲁因因子接近 1，部分案例的检查速度达到 Lean 的 10–100 倍。其验证记录支持交互式阅读、书写与修正，并在初步 AI 智能体实验中展现出潜力。它还能将支持的证明编译到 Lean，作为前端语言，为后续独立复核提供途径。

<a id="readme-comparisons"></a>

## 熟悉的表达，熟悉的数学

同样的数学，用 Litex 和 Lean 分别这样书写。点击例子可查看文末的完整代码。

| 数学表达 | Litex | Lean（使用 `import Mathlib`） |
| --- | --- | --- |
| [自然数算术：1 + 1 = 2](#readme-example-nat_mathlib) | `1 + 1 = 2` | `example : (1 : Nat) + 1 = 2 := by rfl` |
| [任取正实数，推出它不等于零](#readme-example-positive_nonzero) | `forall x R: x > 0 => x != 0` | `example (x : ℝ) (hx : x > 0) : x ≠ 0 := by` |
|  |  | `  exact ne_of_gt hx` |
| [存在平方为 4 的实数；取 2 为见证](#readme-example-square_witness) | `witness exist w R st {w^2 = 4} from 2` | `example : ∃ w : ℝ, w ^ 2 = 4 := by` |
|  |  | `  refine ⟨2, ?_⟩` |
|  |  | `  norm_num` |
| [定义并调用非零实数上的倒数函数](#readme-example-guarded_reciprocal) | `have fn reciprocal(x R: x != 0) R = 1 / x` | `noncomputable def reciprocal (x : {y : ℝ // y ≠ 0}) : ℝ :=` |
|  | `reciprocal(2) = 1 / 2` | `  (x : ℝ)⁻¹` |
|  |  |  |
|  |  | `example : reciprocal ⟨2, by norm_num⟩ = (2 : ℝ)⁻¹ := by` |
|  |  | `  simp [reciprocal]` |

### 表达长度与检查速度

德布鲁因因子越小，表达越简短；耗时以毫秒计，加速比越大，表示 Litex 检查越快。

| 数学任务 | Litex 德布鲁因因子 ↓ | Lean 德布鲁因因子 ↓ | Litex（毫秒）↓ | Lean（毫秒）↓ | Litex 加速比 ↑ |
| --- | ---: | ---: | ---: | ---: | ---: |
| [对数：log₂8 = 3](#readme-example-log_2_8) | 0.48 | 5.95 | 0.064 | 13.992 | **217.0×** |
| [数论：1000000007 是素数](#readme-example-prime_1000000007) | 0.55 | 1.33 | 0.027 | 4.029 | **147.2×** |
| [集合论：正实数集合非空](#readme-example-witness_nonempty_positive) | 0.54 | 1.07 | 0.084 | 6.439 | **76.9×** |
| [定义并调用“正实数非零”定理](#readme-example-named_theorem) | 1.43 | 2.33 | 0.158 | 8.018 | **50.7×** |
| [定义开区间谓词并验证成员](#readme-example-predicate) | 0.88 | 1.52 | 0.189 | 8.223 | **43.4×** |
| [自然数算术：1 + 1 = 2](#readme-example-nat_mathlib) | 1.00 | 5.20 | 0.037 | 1.361 | **36.7×** |
| [全称命题：两个正实数之和为正](#readme-example-forall_add_pos) | 0.57 | 1.34 | 0.392 | 10.487 | **26.7×** |
| [平方函数在 3 处的导数为 6](#readme-example-derivative_square_at_three) | 0.51 | 1.34 | 1.464 | 29.945 | **20.5×** |

## 为什么构建 Litex

**数学本身能不能就是形式化语言？** 数学书写已经在引入对象、给出定义、陈述前提与论证结论。我希望保留这种对应，只加入足以让机器严格检查的结构。

我希望 Litex 成为形式化数学中的 Python：写法熟悉、约定少，语言替用户承担必要的底层工作。AI 产生的候选推理越多，我们用什么语言理解、检查和传递数学知识，就越重要。

## 从数学语言到可检查的知识

**数学基础。** Litex 使用集合、元素、函数与关系。常见运算带着明确的使用条件：`1 - 2 = -1`，而 `1 / 0` 因无定义被拒绝。函数可以直接把必要条件放进定义域：

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

`reciprocal(0)` 会被拒绝，因为参数不满足非零条件。

**语法。** 类似 Python 的缩进组织作用域与推理。开头的全称陈述中，`x R` 引入实数，`x > 0` 是前提，`x != 0` 是待检查的结论。较长的证明仍需作者给出数学路线，包括中间事实、见证、归纳或分情形。

**语义。** 每条陈述都需要先满足良定义性，再从当前上下文获得证明依据。检查器用 JSON 返回判定、依据与存入的事实。例如，`1 + 1 = 2` 的英文输出节选为：

```json
{
  "statement_result": "accepted",
  "statement": "(1 + 1) = 2",
  "proof_method": { "type": "by_closed_calculation" },
  "stores": ["(1 + 1) = 2"]
}
```

换成 `1 / 0 = 0`，输出会指出无法满足的条件 `0 != 0`。反馈支持包括中文在内的十种语言；使用 `-lang zh` 切换为中文。

**架构：证明作为搜索。** 看这两行：

```litex
let a = 1
a + 2 = 3
```

第一行存下 `a = 1`。第二行成为查询：找到这条等式，代入得到 `1 + 2 = 3`，再完成计算。通过检查的 `a + 2 = 3` 又成为后续步骤可使用的知识。

Litex 把数学特化的事实数据库、有界局部搜索与几百条内置规则结合起来。上下文提供事实，规则把事实连接起来，计算也是其中一种检查方法。搜索没有找到依据，只表示当前步骤未被证明，不等于证明了它的否定。

## 让同一份数学连接更多工具

实验性的 `litex -lean -f proof.lit` 编译器可以生成 Lean 陈述和证明，交给 Lean 内核独立检查，让用户用 Litex 书写数学，并在支持的范围内接入 Lean 生态。

同一份源码与验证记录还可以用于：

- **交互式教材：** `litex -reading -f proof.lit` 打开源码，支持查看定义、参数范围与证明引用，并可编辑、检查。
- **LaTeX：** `litex -latex -f proof.lit` 将数学定义和陈述排版为文档。
- **C 与 Python：** 实验性的代码提取可以把支持的计算定义转成可运行的程序。

## 与 AI 一起构建数学

人或智能体可以提出一步，读取反馈，修正后继续。保持同一个 Session，普通拒绝后仍能使用此前接受的定义和事实。

在包含 **165 项数学任务** 的平面几何建库实验中，`deepseek-chat` 取得了以下结果：

| 自动建库运行 | Litex | Lean |
| --- | ---: | ---: |
| 总耗时 | **14.3 分钟** | **177.5 分钟** |

这次实验中，Litex 的建库速度约为 Lean 的 **12.4 倍**。其他工程包括智能体书写的 IMO 几何证明，以及证明技巧、代数、分析和几何等教材。

## 试用 Litex

可以在官网在线试用，也可以在 macOS / Linux 上用 Homebrew 安装：

```bash
brew install litexlang/tap/litex
litex -e '1 + 1 = 2'
```

Windows 已安装 Scoop 和 Git 时运行：

```powershell
scoop bucket add litex https://github.com/litexlang/scoop-litex
scoop install litex
```

把附录中任意一个完整的 Litex 例子保存为 `proof.lit`，运行 `litex -strict -f proof.lit`。交互书写时运行：

```bash
litex -strict -session -e 'let a = 1'
```

输入 `a = 2` 会被拒绝，接着输入 `a + 2 = 3`，仍能使用保留的上下文通过检查。书写时保持这个 Session，将接受的源码保存下来，在阶段完成时单独检查文件。`litex -help` 可查看命令。

Litex 仍处于 beta 阶段。`-strict` 拒绝用户书写的 `trust` 和 `axiom`；验证仍依赖 Litex 的检查器与数学基础。

## 关于

我是沈嘉辰（Jiachen Shen），复旦大学数学博士生。我希望 Litex 让更多人能够书写可检查的数学，也理解其中的定义、条件与推理。欢迎交流与反馈：litexlang@outlook.com。

特别感谢 Wei Lin、Siqi Sun、Peng Sun、Chenxuan Huang、Yan Lu、Sheng Xu、Keyao Zhu 与 Zhaoxuan Hong 的支持和建议。

以 Apache License 2.0 发布。

## 附录：完整例子

每个例子可独立运行；点击标题展开 Litex 与 Lean 的完整代码。

<details id="readme-example-nat_mathlib">
<summary>1. 自然数算术：1 + 1 = 2</summary>

**Litex**

```litex
1 + 1 = 2
```

**Lean**

```lean
import Mathlib

example : (1 : Nat) + 1 = 2 := by rfl
```

[返回对比表](#readme-comparisons)

</details>

<details id="readme-example-positive_nonzero">
<summary>2. 任取正实数，推出它不等于零</summary>

**Litex**

```litex
forall x R:
    x > 0
    =>:
        x != 0
```

**Lean**

```lean
import Mathlib

example (x : ℝ) (hx : x > 0) : x ≠ 0 := by
  exact ne_of_gt hx
```

[返回对比表](#readme-comparisons)

</details>

<details id="readme-example-square_witness">
<summary>3. 存在平方为 4 的实数；取 2 为见证</summary>

**Litex**

```litex
witness exist w R st {w^2 = 4} from 2
```

**Lean**

```lean
import Mathlib

example : ∃ w : ℝ, w ^ 2 = 4 := by
  refine ⟨2, ?_⟩
  norm_num
```

[返回对比表](#readme-comparisons)

</details>

<details id="readme-example-guarded_reciprocal">
<summary>4. 定义并调用非零实数上的倒数函数</summary>

**Litex**

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

**Lean**

```lean
import Mathlib

noncomputable def reciprocal (x : {y : ℝ // y ≠ 0}) : ℝ :=
  (x : ℝ)⁻¹

example : reciprocal ⟨2, by norm_num⟩ = (2 : ℝ)⁻¹ := by
  simp [reciprocal]
```

[返回对比表](#readme-comparisons)

</details>

<details id="readme-example-log_2_8">
<summary>5. 对数：log₂8 = 3</summary>

**Litex**

```litex
log(2,8)=3
```

**Lean**

```lean
import Mathlib

example : Real.logb 2 8=3 := by
  rw [show (8:Real)=2^3 by norm_num, Real.logb_pow]
  rw [Real.logb_self_eq_one (by norm_num : (1:Real)<2)]
  norm_num
```

[返回对比表](#readme-comparisons)

</details>

<details id="readme-example-prime_1000000007">
<summary>6. 数论：1000000007 是素数</summary>

**Litex**

```litex
$prime(1000000007)
```

**Lean**

```lean
import Mathlib

example : Nat.Prime 1000000007 := by native_decide
```

[返回对比表](#readme-comparisons)

</details>

<details id="readme-example-witness_nonempty_positive">
<summary>7. 集合论：正实数集合非空</summary>

**Litex**

```litex
witness $is_nonempty_set({x R:x>0}) from 1
```

**Lean**

```lean
import Mathlib

example : Set.Nonempty {x : Real | 0 < x} := ⟨(1 : Real), (show (0 : Real) < 1 from zero_lt_one)⟩
```

[返回对比表](#readme-comparisons)

</details>

<details id="readme-example-named_theorem">
<summary>8. 定义并调用“正实数非零”定理</summary>

**Litex**

```litex
thm bench_positive_is_nonzero:
    ? forall x R:
        x>0
        =>:
            x!=0
release thm bench_positive_is_nonzero(3)
```

**Lean**

```lean
import Mathlib

theorem bench_positive_is_nonzero : ∀ x : Real, 0 < x → x ≠ 0 := by
  intro x hx
  exact ne_of_gt hx
theorem bench_use : (3 : Real) ≠ 0 := bench_positive_is_nonzero 3 (by norm_num)
```

[返回对比表](#readme-comparisons)

</details>

<details id="readme-example-predicate">
<summary>9. 定义开区间谓词并验证成员</summary>

**Litex**

```litex
prop bench_in_open(x,a,b R):
    a<x
    x<b
by def $bench_in_open(1,0,2)
```

**Lean**

```lean
import Mathlib

def bench_in_open (x a b : Real) : Prop := a < x ∧ x < b
theorem bench_use : bench_in_open 1 0 2 := by norm_num [bench_in_open]
```

[返回对比表](#readme-comparisons)

</details>

<details id="readme-example-forall_add_pos">
<summary>10. 全称命题：两个正实数之和为正</summary>

**Litex**

```litex
forall x,y R:
    x > 0
    y > 0
    =>:
        x+y > 0
```

**Lean**

```lean
import Mathlib

theorem bench : ∀ x y : Real, 0 < x → 0 < y → 0 < x+y := fun x y hx hy => add_pos hx hy
```

[返回对比表](#readme-comparisons)

</details>

<details id="readme-example-derivative_square_at_three">
<summary>11. 平方函数在 3 处的导数为 6</summary>

**Litex**

```litex
$has_derivative_at(fn(t R) R {t^2},3,6)
```

**Lean**

```lean
import Mathlib

theorem bench : HasDerivAt (fun t : Real => t ^ 2) 6 3 := by have h := hasDerivAt_pow 2 (3 : Real); norm_num at h; exact h
```

[返回对比表](#readme-comparisons)

</details>
