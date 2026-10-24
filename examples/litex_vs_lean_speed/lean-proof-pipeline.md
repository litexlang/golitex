# 为什么Litex计算1+1=2比Lean快了30倍？截然不同的运行架构和对数学证明的理解的选择。

先弄清 Lean 实际做了什么，再讨论 Litex 可能省下哪部分工作。这一页是后续故事型比较的第一步，**没有新增计时结果**。

## 1. 源码先成为一个待填的证明

实测环境为 Lean 4.31.0，使用 `import Lean`，没有导入 Mathlib：

```lean
theorem one_add_one : (1 : Nat) + 1 = 2 := by rfl
```

Lean 把命题当作类型，把证明当作具有这个类型的项。这里的任务是构造一个 `p`，使得 `p : (1 : Nat) + 1 = 2`。[官方：命题与证明](https://lean-lang.org/theorem_proving_in_lean4/Propositions-and-Proofs/)

这条路径可概括为下面的教学示意。宏展开和 elaboration 在实际实现中可以交错进行，不是每个阶段都只走一次：

```text
源码
  → 解析后的语法树
  → 宏展开、elaboration：确定类型、实例、隐式参数，执行 tactic
  → 核心类型论中的「命题类型 + 证明项」
  → kernel 检查证明项的类型是否与命题相符
  → 接受声明，供后续命题引用
```

这里的 elaboration 是把便于书写的语法变成显式核心项。可执行函数另有编译到 C 和本机代码的路径；检查这条等式不需要先把它的证明编译成一个 C 程序。[官方：处理流程、内核与编译](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)

## 2. `+`、数字和 `=` 逐渐变得显式

以下是**教学伪代码**，省略 universe 参数和若干实例参数；这些箭头表示解释层次，不表示完整执行日志：

```text
(1 : Nat) + 1 = 2
    ↓ 确定 + 使用 Nat 的加法实例，数字使用 Nat 的 OfNat 实例
Eq Nat (HAdd.hAdd Nat Nat Nat natAddInstance 1 1) 2
    ↓ 展开对应实例和数字包装
Eq Nat (Nat.add 1 1) 2
```

`Eq Nat a b` 可读作“自然数 a 等于 b 的证明类型”。真实 `pp.all` 输出中的命题是：

```lean
@Eq.{1} Nat
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
```

这里的 `@` 让隐式参数显式出现。这段比较长，主要是加法和数字的通用接口已经显式化；它不是一次庞大的数学证明。

## 3. `rfl` 构造了什么？

实际执行 `#print one_add_one` 的输出是：

```lean
theorem ProofPipeline.one_add_one : 1 + 1 = 2 :=
Eq.refl (1 + 1)
```

`Eq.refl a` 是等式的自反性构造器，类型是 `a = a`。下面是本例的**简化核心项**，省略了实例包装和 universe：

```text
目标类型： Eq Nat (Nat.add 1 1) 2
证明项：   Eq.refl Nat (Nat.add 1 1)
项的类型： Eq Nat (Nat.add 1 1) (Nat.add 1 1)
```

因此，tactic 在本例中留下的是一个很小的构造器应用。tactic 的角色是生成证明项；内核随后检查该项。内核不需要重新运行 `rfl` 脚本。[官方：tactic 与证明项](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/)

## 4. 为什么 `a = a` 能证明 `1 + 1 = 2`？

因为这里的两个类型在计算后相同，这叫定义相等。下面是**检查器的教学伪代码**，不代表 Lean 内核的具体函数实现或完整调用次数：

```text
goal := Eq Nat (Nat.add 1 1) 2
proof := Eq.refl Nat (Nat.add 1 1)

inferred := inferType(proof)
// Eq Nat (Nat.add 1 1) (Nat.add 1 1)

accept if definitionallyEqual(inferred, goal)
// 在比较过程中，Nat.add 1 1 可以计算成 2
```

用自然数加法的逻辑定义演示这次计算，可以写成：

```text
add a zero     ↦ a
add a (succ b) ↦ succ (add a b)

add 1 1 ↦ succ (add 1 0) ↦ succ 1 ↦ 2
```

**这只是逻辑模型，不是实际的性能轨迹。** Lean 对自然数常量、加法等有内核优化，使用高效的任意精度整数实现；不能由这个演示推断它按数值大小逐个展开 `succ`。本机 `#print Nat.add` 还显示了递归定义转换后的 `Nat.brecOn` 形式，完整输出已保留。[官方：自然数实现](https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/)，[本次版本源码](https://github.com/leanprover/lean4/blob/v4.31.0/src/Init/Prelude.lean)

另一个实际通过的写法是：

```lean
theorem one_add_one_term : (1 : Nat) + 1 = 2 := @Eq.refl Nat 2
```

它直接提供 `2 = 2` 的证明项，仍可通过定义相等匹配目标。说明 elaborator 无须每次都保留同一种语法形状，也无须构造一长串算术等式证明。

## 5. lambda 在哪里？

Lean 的核心是带依赖类型、归纳类型等构造的类型论。不能把它理解成“所有数字都变成 Church numeral 的纯无类型 lambda calculus”。本例的封闭证明只有常量和函数应用，根本不需要 lambda 抽象。

加入一个变量，就能实际看到 lambda：

```lean
theorem add_one (n : Nat) : n + 1 = Nat.succ n := by rfl
```

真实 `#print` 输出：

```lean
theorem ProofPipeline.add_one : ∀ (n : Nat), n + 1 = n.succ :=
fun n => Eq.refl (n + 1)
```

下面是它的**伪依赖 lambda 表达式**，仍省略实例和 universe：

```text
类型： Π n : Nat, Eq Nat (Nat.add n 1) (Nat.succ n)
证明： λ n : Nat. Eq.refl Nat (Nat.add n 1)
```

`Π n` 表示“对每个 n 都有一个证明”，`λ n` 则是给定 n 后返回相应证明的函数。原始 `Expr` 输出也确认：命题外层是 `Lean.Expr.forallE`，证明外层是 `Lean.Expr.lam`。这里的 `Nat.add n 1` 依定义得到 `Nat.succ n`，所以函数体仍然只需自反性。

## 6. 这给 Litex 比较留下什么问题？

对闭合等式，当前 Litex 源码中有这条专门计算路径：

```rust
pub fn calculate_closed_equal_fact(fact: &EqualFact) -> Option<ClosedEqualityCalculationProof> {
    let (values, equal) = calculate_value_pair(&fact.left, &fact.right)?;
    equal.then_some(ClosedEqualityCalculationProof { values })
}
```

它计算两边并返回相应证据，见 [源码](../../src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/calculate_closed_equal_fact.rs)。这提示了一个待测假设：某些专门事实规则可能减少通用 elaboration、核心证明项构造和类型检查的工作。但 Litex 仍有解析、良定义性检查、验证和证据构建等成本；若生成 Lean 证明再检查，还会另加那条路径的成本。

`1 + 1 = 2` 同时提供了这个假设的边界：Lean 在这里的证明项很小，自然数计算也有优化。单凭“Lean 基于 lambda calculus”无法推出它慢，更无法解释已有总耗时的全部差异。后续应分别测 elaboration、证明项构造、内核检查，以及 Litex 的对应成本，并保留 Lean 的直接证明项路线作对照。

## 实测记录

- [完整可运行源码](sources/lean-proof-pipeline/OnePlusOne.lean)：三个定理、普通和显式打印、自然数归约、原始 `Expr`。
- [真实标准输出](results/lean-proof-pipeline-output.txt)：成功退出，三个定理的 `#print axioms` 都报告没有公理依赖。
- [验证与负例](results/lean-proof-pipeline-validation.json)：把右侧改为 `3` 的 `by rfl` 被拒绝，进程退出码为 1。
- 没有 `sorry`、用户公理或新增计时数据。官方 latest 手册用于解释架构；实际证明项以本次 Lean 4.31.0 输出为准。
