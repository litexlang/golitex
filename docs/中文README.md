<div align="center">
  <img src="../assets/logo.PNG" alt="Litex logo" width="300">

# Litex

### 形式化数学的高级语言
*(The High-Level Language for Formal Mathematics · 形式化数学的 Python)*

由沈嘉辰创建和维护。

[官网与在线体验](https://litexlang.com/) · [Litex 蓝图](Litex中文蓝图.md) · [学习手册](Litex手册.md) · [安装指南](安装Litex.md) · [Zulip 社区](https://litex.zulipchat.com/) · [English README](../README.md)
</div>

---

## 什么是 Litex？

**Litex 是一门面向形式化数学的高级编程语言。**

在计算机科学的发展历程中，编程经历了从机器指令（0101）到汇编语言，再到 C、Python 等高级语言的演进。高级语言通过抽象掉寄存器、栈帧和内存地址管理，让程序员得以直接在问题层面表达算法与架构。

今天的形式化数学，正在经历完全相同的演进历程：

```text
┌────────────────────────────────────────────────────────────────────────┐
│                               Litex                                    │
│                         形式化数学的高级语言                            │
│    • 数学本位直观陈述                • 自动良定义与定义域检测          │
│    • 编译器有界自动推理              • AI Agent 原生交互会话 (Session) │
└───────────────────────────────────┬────────────────────────────────────┘
                                    │ 编译与重放证明
              ┌─────────────────────┼─────────────────────┐
              ▼                     ▼                     ▼
       ┌──────────────┐      ┌──────────────┐      ┌──────────────┐
       │    Lean 4    │      │  Coq / Rocq  │      │   Isabelle   │
       │    Kernel    │      │    Kernel    │      │    Kernel    │
       └──────────────┘      └──────────────┘      └──────────────┘
              ▲                     ▲                     ▲
              └─────────────────────┴─────────────────────┘
                             底层形式化验证内核
```

目前，主流交互式证明助手（如 Lean、Coq、Isabelle）在体验上仍处于形式化数学的“汇编时代”。用户需要耗费海量的认知精力处理底层证明指令流：操纵策略（tactic）、管理目标栈（goals）、手写 `intro`、`apply`、`simp`、`rewrite`，以及与复杂的依值类型（Dependent Type）和子类型强制转换搏斗。

**Litex 将高级语言范式引入形式化数学：**
1. **数学本位（Math-Centric）**：像在教科书上写数学一样，用清晰、现代的 Python 式缩进直接陈述对象、定义与推导步骤，而非编写繁琐的策略脚本。
2. **自动化繁重机械工作**：编译器在幕后自动完成良定义性（Well-Definedness）检测、定义域条件验证、代入化简与上下文事实检索。
3. **通用高级前端（Universal Frontend）**：Litex 并不试图取代形式化验证内核，而是为它们提供统一的高级抽象层。在 Litex 中通过验证的证明，可直接编译至 **Lean 4**、**Coq**、**Isabelle** 等底层证明助手，由其内核进行最终的严谨独立复核。

---

## 核心设计支柱

### 1. 数学本位：陈述数学，而非编织策略

Litex 的源码贴近人类数学思维。没有晦涩的策略命令流，数学语句本身就构成了代码的结构：

```litex
forall x R:
    x^2 >= 0
```

`forall` 表达全称量词，`R` 声明实数载体，`x^2 >= 0` 是直接陈述的事实。作者专注于数学主线，系统负责检索依据并验证步步成立。

### 2. 自动检测良定义与定义域（Well-Definedness Checking）

在传统形式化系统里，部分函数（如除法 $1/x$、开方 $\sqrt{x}$、数列下标越界）的定义域处理极其繁琐，常常需要在每一次调用时手动携带并打包子类型证明项。

**在 Litex 中，数学的良定义性是语言的第一公民保障：**

```litex
# 定义一个受 x != 0 守卫的倒数函数
have fn reciprocal(x R: x != 0) R = 1 / x

# 传入合法参数，自动完成检查并使用：
reciprocal(2) = 1 / 2
```

如果作者（或 AI）写出 `reciprocal(0)`，Litex 不会给出云里雾里的策略报错，而是在证明开始前的**良定义性（Well-Definedness）阶段**立即拦截并明确指出：

```text
WellDefinedError: object reciprocal(0) is not well-defined
  --> failed to verify function domain fact: 0 != 0
```

你只管展开数学论证，语言底层自动为你兜底定义域的合法性。

### 3. 检查器承担机械推理：约 35 万行纯 Rust 引擎

Litex 背后凝聚着约 35 万行精心优化的 Rust 代码，只为两件事：**语言自然易写，检查极致飞快。**

对每一步数学陈述，Litex 执行严格有界的闭环验证：
1. **检索**：在当前作用域中定位相关定义、已接受事实与内置公理规则。
2. **校验**：检查良定义性、匹配参数并验证所有前置条件。
3. **提交**：记录完整的成立依据，并将确认的事实提交到上下文，供后续步骤直接使用。

作者负责构思核心跳跃——引理选择、辅助见证（Witness）、分类讨论或数学归纳；Litex 负责在毫秒内自动补齐中间的代数变形与逻辑衔接。

### 4. 为 AI 数学研究原生设计（Agent-Native）

Litex 是天生适合大语言模型（LLM）与数学智能体（AI Agent）的形式化基座：

* **自然易学的语法**：类似 Python 的优雅排版，极易被大模型理解与生成，不再困死在复杂的元编程与策略语法陷阱中。
* **持续会话机制 (`litex -session`)**：传统证明助手在单步出错时往往直接挂起或重置状态。Litex 提供持久化 REPL，**单步尝试失败绝不会抹去之前已接受的上下文**。智能体可以一步步探索，出错即时在原地修复并推进。
* **结构化精准反馈**：当智能体漏写了 $x \neq 0$ 或越界条件时，Litex 返回精确的结构化 JSON 诊断，告知哪一条定义域条件未被满足，使得大模型具备了零样本自我修正（Self-Correction）的可能。

```bash
litex -strict -session -e 'have a R = 2'
litex> a = 3
# {"run_result": "failure", "session_terminated": false}
litex> a + 1 = 3
# {"run_result": "success", "session_terminated": false}
```

### 5. 一处编写，流向多元生态

同一份 Litex 数学成果，可以一键连通多个下游应用：

* **编译至底层内核（Lean 4 / Coq / Isabelle）**：通过 `litex -lean -f proof.lit`，将已验证的推导重放生成独立的 Lean 4 证明，接受 Lean 内核二次复核。架构面向 Coq 与 Isabelle 保持通用。
* **一键导出出版级 LaTeX**：通过 `litex -latex -document -f proof.lit` 直接生成论文排版。
* **交互式教材与知识图谱**：通过 `litex -reading` 探索定理依赖关系网与依据追溯。
* **可执行代码抽取**：把数值与算法定义直接抽取为 Python 或 C 程序（`litex -extractpython`, `litex -extractc`）。

---

## 快速上手

### 安装

**macOS / Linux（Homebrew）：**
```bash
brew install litexlang/tap/litex
```

**Windows（Scoop）：**
```powershell
scoop bucket add litex https://github.com/litexlang/scoop-litex
scoop install litex
```

**网页免安装试玩：** 访问 [litexlang.com](https://litexlang.com/) 即可直接在浏览器中体验。

### 常用命令

```bash
# 单行事实直接验证
litex -e '1 + 1 = 2'

# 开启交互式数学会话
litex -session

# 验证数学证明文件
litex -f proof.lit

# 将 Litex 证明编译为 Lean 4 代码
litex -lean -f proof.lit

# 导出完整的 LaTeX 文档
litex -latex -document -lang zh -f proof.lit
```

---

## 完整示例：证明 √2 是无理数

假设 $\sqrt{2}$ 是有理数，可设为既约分数 $p/q$。简单的整除性推导表明 $p$ 与 $q$ 必须同时为偶数，从而与互质产生矛盾：

```litex
# 证明 sqrt(2) 不是有理数
by contra:
    ? not sqrt(2) $in Q
    release thm rational_has_unique_reduced_fraction(sqrt(2))
    obtain p, q from exist! p Z, q N+ st {sqrt(2) = p / q, gcd(p, q) = 1}

    p^2 = (sqrt(2) * q)^2 = sqrt(2)^2 * q^2 = 2 * q^2
    p^2 % 2 = (2 * q^2) % 2 = 0
    release thm prime_divides_power(p, 2, 2)

    p / 2 $in Z
    q^2 = p^2 / 2 = 2 * (p / 2)^2
    q^2 % 2 = (2 * (p / 2)^2) % 2 = 0
    release thm prime_divides_power(q, 2, 2)

    impossible 2 <= gcd(p, q) = 1
```

作者只需指出关键的既约分解定理并写出核心算式链，Litex 自动校验奇偶性、代数代换与矛盾闭环。

---

<a id="readme-comparisons"></a>
<a id="表达长度与检查速度"></a>

## 检查性能速览

得益于纯 Rust 编写的特化演绎引擎，Litex 的单步验证均在亚毫秒级别完成。

| 数学任务 | Litex（毫秒）↓ | Lean（毫秒）↓ | Lean ÷ Litex |
| --- | ---: | ---: | ---: |
| [正实数集合非空见证](#readme-example-witness_nonempty_positive) | 0.084 | 6.439 | **76.9×** |
| [自然数算术：1 + 1 = 2](#readme-example-nat_mathlib) | 0.037 | 1.361 | **36.7×** |
| [全称命题：正实数之和为正](#readme-example-forall_add_pos) | 0.392 | 10.487 | **26.7×** |
| [平方函数在 3 处的导数为 6](#readme-example-derivative_square_at_three) | 1.464 | 29.945 | **20.5×** |

*(基于本地历史测试中位数，不计进程启动与模块导入耗时。详见[测量方法报告](../examples/litex_vs_lean_speed/README.md)。)*

---

<a id="litex-reliability"></a>

## 项目现状与作者

Litex 是始于 2024 年的独立研究项目，由复旦大学数学博士生**沈嘉辰（Jiachen Shen）**创建并维护。

目前项目处于活跃的 **Beta** 测试阶段。我们正在持续扩充语言特性、标准库定理以及底层形式化编译后端。如果你发现任何 Bug 或有建议，欢迎提交最小复现用例！

* **官方网站**：[litexlang.com](https://litexlang.com/)
* **社区讨论**：[Zulip](https://litex.zulipchat.com/)
* **GitHub Issues**：[github.com/litexlang/golitex/issues](https://github.com/litexlang/golitex/issues)
* **联系邮箱**：litexlang@outlook.com

特别感谢 Wei Lin、Siqi Sun、Peng Sun、Chenxuan Huang、Yan Lu、Sheng Xu、Hao Wu、Keyao Zhu 与 Zhaoxuan Hong 的支持和建议。

遵循 [Apache License 2.0](LICENSE) 开源协议。

---

## 附录：完整对照用例

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
