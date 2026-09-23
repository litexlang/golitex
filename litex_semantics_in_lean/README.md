# 新的Litex到Lean的语义接口设计

```text
Litex 语义对象
    = 宿主 Lean 载体中的代表元
    + Litex 的语义关系

Litex 的 Same
    = 复数 C 的运算规律
    + 集合外延性
    + 等价关系闭包

Lean 的 Eq
    = 适配器层恢复出来的宿主相等
```

`Core.lean` 不应该复制 Rust 的 `Obj`、`Stmt`、`Fact` 枚举，而应该提供这些枚举最终可以落到的语义接口。

---

# 一、Core.lean 的总体分层

建议把 `Core.lean` 分成六层。

## Layer 0：可信边界

这一层规定什么可以进入 Lean kernel。

安全 Core 中禁止：

```lean
axiom
sorry
admit
unsafe theorem
```

Rust verifier 产生的 `FactId`、`BuiltinRuleId`、`BuiltinRuleEvidence` 都不能直接变成 Lean 公理。它们必须映射到 Core 中的已证明定理。

未完成的 Litex `axiom`、`abstract_prop`、`trust` 可以保留，但必须进入独立的可信债务层，例如：

```lean
namespace Litex.Trusted
```

普通 Mathlib 风格的 `Final.lean` 不应自动导入这一层。

---

## Layer 1：宿主载体与语义对象

Lean 仍然需要类型，因为 Lean 的函数、归纳类型和证明都依赖类型。

但是 Litex 不把宿主类型当成对象本质。

概念上，一个 Litex 对象类似：

```lean
Σ α : Type, α
```

也就是：

```text
某个宿主载体 α
+
其中的代表值 x
```

但这个 sigma 类型只应作为编译器内部概念，不能暴露成新的万能：

```lean
LitexObject
```

否则又会回到“所有东西都装进一个大盒子”的设计。

公开 Core API 仍然使用：

```lean
x : α
y : β
```

而通过异质的 `Same` 连接它们。

---

# 二、`Same`：Litex 世界的核心语义关系

第一版建议：

```lean
universe u v

inductive Same :
    {α : Type u} →
    {β : Type v} →
    α →
    β →
    Prop
```

`Same` 的生成来源只允许三类。

## 1. 宿主 Lean 已知的相等

```lean
Same.ofEq : x = y → Same x y
```

这个不是 Litex 的新语义规则，只是把 Lean 已经证明的同载体相等注入 Litex。

## 2. 复数语义规律

例如：

```text
1 + 1 Same 2
(3 : ℕ) Same (3 : ℂ)
(1 + i) * (1 - i) Same 2
```

这些都来自 Litex 对 `C` 的运算语义。

可以在 Core 内部定义一个封闭的复数语义证书：

```lean
inductive ComplexLaw :
    {α : Type u} →
    {β : Type v} →
    α →
    β →
    Prop
```

但不允许用户随意构造任意 `ComplexLaw`。它的构造器只由 Core 和经过审查的规则模块提供。

然后：

```lean
Same.ofComplexLaw :
  ComplexLaw x y → Same x y
```

## 3. 集合外延性

如果两个对象都是集合，并且成员完全相同，那么它们 `Same`。

```lean
Same.ofSetExt :
  IsSet A →
  IsSet B →
  (∀ x, In x A ↔ In x B) →
  Same A B
```

最后只有等价关系闭包：

```lean
Same.refl
Same.symm
Same.trans
```

因此第一版的语义基底可以明确写成：

```text
Same = Eq injection
     + Complex laws
     + Set extension
     + reflexive/symmetric/transitive closure
```

当前 `PrimitiveRule` / `DerivedRule` 的公开任意注册方式应该移除或封闭，否则用户能够用 `relation := True` 制造非法 `Same`。

---

# 三、集合、`In`、`IsSet`

这是整个体系中最重要的部分。

## 1. 精确集合载体

```lean
structure Set.{v} where
  Carrier : Type v
```

集合的元素载体是精确的 Lean 类型，而不是统一的 `LitexObject`。

例如：

```lean
Litex.N : Litex.Set := ⟨ℕ⟩
Litex.Z : Litex.Set := ⟨ℤ⟩
Litex.Q : Litex.Set := ⟨ℚ⟩
Litex.R : Litex.Set := ⟨ℝ⟩
Litex.C : Litex.Set := ⟨ℂ⟩
```

## 2. 集合成员

必须支持跨 universe、跨载体：

```lean
def In
    {α : Type u}
    (x : α)
    (S : Litex.Set.{v}) : Prop :=
  ∃ y : S.Carrier, Same x y
```

因此：

```lean
In (3 : ℕ) Litex.Z
In (3 : ℤ) Litex.R
In (3 : ℚ) Litex.C
```

都可以成立。

`In` 表达的是：

```text
x 是某个集合载体中某个代表元的 Litex 同一对象
```

而不是 Lean 的普通类型转换。

## 3. 任意对象的集合解释

有些对象本身不是 `Litex.Set`，但可以被解释为集合。

```lean
structure SetView
    {α : Type u}
    (a : α) where
  set : Litex.Set.{v}
  same : Same a set
```

定义：

```lean
def IsSet (a : α) : Prop :=
  Nonempty (SetView a)
```

这里的 `IsSet` 不能简单定义成“有某个 Lean 类型”，而应该表示：

```text
该 Litex 对象拥有一个经过 Same 认证的集合解释
```

任意两个合法的 `SetView` 最终都应该由 `Same` 连接起来，因此成员关系不能依赖于某个不稳定的类型类实例。

## 4. 外延性

```lean
def SetExtensional
    (A B : α) : Prop :=
  ∀ {γ : Type w} (x : γ),
    In x A ↔ In x B
```

实际定理：

```lean
theorem Same.ofSetExt
    {A : α} {B : β}
    (hA : IsSet A)
    (hB : IsSet B)
    (h :
      ∀ {γ : Type w} (x : γ),
        In x A ↔ In x B) :
    Same A B
```

这个接口必须成为：

- 集合相等；
- 区间相等；
- 笛卡尔积相等；
- 函数图相等；
- 序列集合相等；
- 矩阵集合相等；

的共同基础。

---

# 四、Complex 语义与 Mathlib 的接口

`C` 不应该是所有 Litex 对象的唯一宿主载体，而应是一个重要的语义观察空间。

定义复数观察：

```lean
class ComplexView (α : Type u) where
  toComplex : α → ℂ
```

第一版提供：

```lean
ComplexView ℕ
ComplexView ℤ
ComplexView ℚ
ComplexView ℝ
ComplexView ℂ
```

对应：

```lean
ℕ → ℂ
ℤ → ℂ
ℚ → ℂ
ℝ → ℂ
ℂ → ℂ
```

`Same` 应保证观察相容：

```lean
theorem Same.complexEq
    [ComplexView α]
    [ComplexView β]
    (h : Same x y) :
    ComplexView.toComplex x =
      ComplexView.toComplex y
```

这只是：

```text
Same ⇒ 复数观察相等
```

不能无条件反过来。

对于 faithful 的载体，再提供显式恢复：

```lean
theorem Same.natEq :
    Same x y → x = y

theorem Same.intEq :
    Same x y → x = y

theorem Same.ratEq :
    Same x y → x = y

theorem Same.realEq :
    Same x y → x = y

theorem Same.complexNativeEq :
    Same x y → x = y
```

因此 Mathlib adapter 可以写：

```lean
have hxy : Litex.Same x y := ...
have hxy' : x = y := Litex.Same.realEq hxy
```

而最终定理仍然是普通 Lean：

```lean
theorem final_theorem (x y : ℝ) : ... := by
  ...
```

---

# 五、所有 Obj 如何落位

Rust 的 `ObjKind` 不能直接等价于 Lean 类型。它应该经过：

```text
Obj
→ 语义族
→ 选定宿主载体
→ well-definedness 证据
→ Lean 项
```

建议映射如下。

| Litex Obj 类别 | Core 位置 |
|---|---|
| Atom、变量、符号 | Lean 局部变量或声明常量 |
| ℕ、ℤ、ℚ、ℝ、ℂ 数值 | 对应 Lean 数值类型，附带 ComplexView |
| ImaginaryUnit、EulerNumber、Pi | `ℂ` 中的命名常量及 ComplexLaw |
| Add/Sub/Mul/Div/Pow | 语义运算接口 + Same 同余定理 |
| Abs、Sqrt、Sin、Cos、Ln | 带定义域/well-definedness 的语义函数 |
| Union、Intersect、SetMinus | `SetView` 和成员谓词 |
| SetBuilder | subtype 或谓词集合 |
| Cart、Tuple、TupleDim | `Prod`、sigma、有限积载体 |
| FnObj、AnonymousFn | 语义函数结构或函数图 |
| FnRange、Replacement | 集合像、函数图像和 `In` |
| Sequence | `ℕ → α` 或带域的函数结构 |
| Matrix | `Fin m → Fin n → α` 或对应结构 |
| Interval、Ray、ClosedRange | subtype 集合 |
| Sum、Product、Reduce | 有限折叠、`Finset` 或受限聚合 |
| StandardSet | Core 中注册的 `Litex.Set` |
| Struct、Template | Lean `structure`、namespace 和生成的接口 |
| BuiltinApp | 已注册的 Core 语义函数 |

重要的是，`ObjKind` 只是来源分类，不是最终语义分类。

例如两个 `Add` 可能分别落到：

```lean
ℕ
ℤ
ℚ
ℝ
ℂ
```

具体载体由 verifier 选出的数值语义决定。

---

# 六、所有 Fact 如何落位

## 1. 等式

Litex 等式统一为：

```lean
x = y  ↦  Litex.Same x y
```

不应直接生成 Lean：

```lean
x = y
```

只有 Adapter 层在知道载体 faithful 时才恢复 Lean `Eq`。

## 2. 集合成员

```lean
x in A  ↦  Litex.In x A
```

## 3. 集合性

```lean
A set  ↦  Litex.IsSet A
```

## 4. 子集

```lean
A subset B
```

编译为：

```lean
∀ x, In x A → In x B
```

## 5. 非空、有限

直接定义在精确载体上：

```lean
Litex.Nonempty A
Litex.Finite A
```

## 6. 全称、存在、合取、析取、否定

使用 Lean 的普通逻辑：

```lean
∀
∃
∧
∨
¬
```

但内部对象和等式仍使用 `Same`、`In`、`IsSet`。

## 7. 函数等式

当前 Rust 中已经存在：

- `HaveFnEqualStmt`
- `by fn_extension`（`new_pipeline`：点态外延 → 普通 `f = g`）
- 对应 verifier evidence

所以函数相等并不是不存在。`$fn_eq` / `$fn_eq_in` 谓词已从 `new_pipeline` 移除。

不过它不应成为 `Same` 的第三种 primitive。函数相等应该通过函数图的集合外延性导出：

```text
逐点 Same
→ 函数图中的有序对相同
→ 函数图集合外延
→ 函数 Same
```

可以提供派生定理：

```lean
theorem Same.fn_of_pointwise
    (h : ∀ x, Same (f x) (g x)) :
    Same f g
```

当函数和值域都在同一个 Lean 载体中时，再通过：

```lean
funext
```

和值域的 `Same → Eq` 适配恢复普通函数相等。

---

# 七、所有 Stmt 如何落位

`Stmt` 不直接对应某一个 Lean 类型，而对应环境中的声明或证明结果。

| Litex Stmt | Lean 结果 |
|---|---|
| `let` | `let` 或局部定义 |
| `have` | 局部证明项 |
| `have fn` | 函数定义或函数图定义 |
| `have set` | `SetView` / `IsSet` 证明 |
| `def` | `def` |
| `struct` | Lean `structure` |
| `template` | 命名空间、结构或生成器接口 |
| `theorem` | `theorem` |
| `axiom` | 仅进入 Trusted 层 |
| `claim` | 待证明 theorem 声明 |
| `proof block` | 证明项和 FactId 记录 |
| `witness` | `Exists.intro` 或集合代表元 |
| `by` 策略 | verifier 证据到 Lean 定理的调用 |
| `command/eval` | 编译期动作，不进入最终 theorem |
| `unsafe` | 不进入安全生成文件 |

每个 Stmt 的编译结果应该是：

```text
环境增量
+ 可引用的公开 Lean 名字
+ FactId / RuleId 元数据
```

而不是只输出一行匿名 theorem。

---

# 八、verify rule 如何接入

Rust verifier 的 builtin rule 不应直接决定 Lean 证明内容，而应通过固定证书协议。

建议结构：

```text
Rust BuiltinRuleEvidence
        ↓
稳定 RuleId
        ↓
Core/Rules 中的 Lean certificate theorem
        ↓
生成 theorem
```

例如：

```text
builtin.numeric.add
→ Litex.Rules.add_complex
→ Litex.Same.ofComplexLaw
```

集合规则：

```text
builtin.set.extensionality
→ Litex.Rules.set_ext
→ Litex.Same.ofSetExt
```

成员规则：

```text
builtin.membership.congr
→ Litex.Rules.in_congr
→ Litex.In.congr
```

规则映射必须 fail closed：

```text
没有注册的 RuleId
→ 编译失败
```

不能生成：

```lean
by sorry
```

也不能生成：

```lean
axiom generated_fact : ...
```

---

# 九、Core 与 Adapter 的边界

`Core.lean` 负责：

```text
Same
In
IsSet
SetExt
ComplexView
语义运算
语义同余
规则证书接口
```

`Rules.lean` 负责：

```text
Litex verifier rule
→ Core 定理
```

`Generated.lean` 负责：

```text
编译器生成的对象、事实和证明
```

`Adapter.lean` 负责：

```text
Litex.Same → Lean Eq
Litex.In → Mathlib Membership
Litex.IsSet → Mathlib Set
Litex ComplexView → ℂ
```

`Final.lean` 只使用：

```lean
ℕ ℤ ℚ ℝ ℂ
Set
Function
Group
Ring
Field
Finset
```

以及少量 Adapter 定理。

---

# 十、第一版真正应该实现什么

不要先重写所有 compiler。建议先实现一个最小但完整的 vertical slice：

```text
ℕ / ℤ / ℚ / ℝ / ℂ
+
Litex.Set
+
Litex.In
+
Litex.IsSet
+
Same
+
SetExt
+
ComplexView
+
三个 builtin rule
+
Generated → Adapter → Final showcase
```

最先完成的几个定理应是：

```lean
Same.natComplex
Same.intComplex
Same.ratComplex
Same.realComplex

Same.ofSetExt
In.congr
Same.complexEq

Same.realEq
Same.complexNativeEq
```

然后做三个 showcase：

1. 不同 Lean 类型的数通过 `Same` 相等；
2. 两个集合通过 extension axiom 相等；
3. Litex 生成的 `Same` 证明经过 Adapter 变成普通 Mathlib 等式。

最终的 Core 语义图应该是：

```text
                 Complex laws
                      │
                      ▼
Eq injection ───► Same ◄─── Set extension
                    │
          ┌─────────┼─────────┐
          ▼         ▼         ▼
         In       IsSet    function graph
          │         │         │
          └──────► Adapter ◄──┘
                       │
                       ▼
                 Mathlib-style Lean
```

这套设计能够同时满足：

- Litex 的“类型不是本体”；
- 集合外延性是相等的核心来源；
- `C` 的运算规律是数值语义的核心来源；
- 所有 Obj 都能落到语义族；
- 所有 Stmt 都能落到声明/环境增量；
- 所有 Fact 都能落到 `Same`、`In`、`IsSet` 或普通逻辑；
- verifier rule 有明确的 Lean 证书入口；
- 最终能够通过很薄的 Adapter 接入 Mathlib；
- 安全 Core 不需要 `sorry` 或项目公理。