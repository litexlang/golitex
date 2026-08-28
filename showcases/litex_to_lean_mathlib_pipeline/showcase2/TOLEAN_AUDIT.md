# ToLean 完成审计：`converges_to_mul_const`

审计更新：2026-08-28

## 结论

如果问题是“当前 `main.lit` 还缺多少能力才能生成 Lean”，答案现在是：
**没有剩余的阻塞缺口**。ToLean 已经从完整 StmtResult 生成两个定义和
`converges_to_mul_const`，并且 Lean kernel 接受该文件。

当前 Mathlib adapter 也已经把生成数列限制到原生 `ℕ` 输入，导出
普通 `ℕ → ℝ` 上的 `Filter.Tendsto`。这一步只使用
`Litex.In.own Litex.N n` 证明当前 `n : ℕ` 是合法输入，不需要也没有
假设任意异构自然数表示之间的函数值相等。

## 原缺口与当前状态

| 原缺口 | 状态 | 通用修复 |
| --- | --- | --- |
| concrete predicate 中的函数 universe 和证据名遮蔽 | 已解决 | 按精确 set carrier 降低参数，局部证据名按 lexical frame 分配 |
| named theorem binder 在函数应用前看不到 membership FactId | 已解决 | 先安装 binder alias/精确表示，再回放依赖它的 WD 和 inference |
| `SuccessVerifyClaimForallResult` 没有局部 theorem consumer | 已解决 | 在当前 proof frame 内编译 forall claim 及其结论 FactId |
| 局部 `obtain` 无法发布 existential projection 和 typed inference | 已解决 | 按 Result 的 witness/body projection 与 infer tree 逐项发布 |
| `witness` 不能组合 `ForallProof` 和 `ByDefStmt` | 已解决 | 统一走局部 statement-result dispatcher |
| `R+`、依赖存在量词与具体 predicate 参数的 Lean 表示 | 已解决 | 使用精确 subtype carrier，并通过 `Litex.Same`/`Litex.In.congr` 运输证明 |
| 绝对值、乘法、除法、顺序链的 Result 证明回放 | 已解决 | 新增的 consumer 只读 typed evidence/FactId，没有加“乘常数保持收敛”builtin |
| 旧 real-sequence source/name matcher | 已删除 | 旧 sequence 定义也走通用 `DefPropStmt` lowering，其生成文件通过 Lean |

## 为什么之前会卡很久

这个例子在数学上很短，但它同时贯穿了 ToLean 之前没有连起来的多个结构：

```text
具体 predicate 定义
  → R+ 的精确 subtype forall
  → 局部 forall claim
  → 从存在量词 obtain 见证
  → 见证内嵌套 forall 和 by def
  → 匿名函数应用
  → 绝对值/除法/乘法/顺序链
  → predicate 的展开与折叠
```

每一步都不能只输出一段“看起来对”的 Lean 字符串；它必须沿用 verifier
选中的 FactId、membership 证明和精确 carrier。最难的部分是，同一个 Litex
实数在不同位置可能分别以 `ℂ`、`ℝ` 或 `R+` subtype 出现；这些不能交给
Lean 猜，必须用显式 `Same` 桥接和 `In.congr` 携带原证明。

所以耗时的不是证明“乘常数保持收敛”，而是把一条以前不完整的通用
StmtResult-to-Lean 路径打通，同时保证没有定理特化、项目公理或证明洞。

## 已消除的原生数列阻塞

原先生成的嵌套 binder 会把普通 `n N` 固定在一个无关的 host carrier 上，
导致 Mathlib adapter 无法直接用 `n : ℕ` 实例化尾部定理。通用修复由四部分组成：

1. 每个普通数值源输入都有自己的隐式 Lean host carrier；
2. 源集合分类仍然由显式 `Litex.In` 承担；
3. 值本身已经在精确 carrier 中时，`Litex.In.rep_exact` 把代表元约简为原值；
4. 整体复用生成的 `forall` 证明时，通过显式 `@` 应用保留隐藏 carrier 参数。

这些都是 forall binder、membership 和 proof replay 的通用规则，没有检查
`converges_to`、数列定理名或整份源文本。

## 仍然保留的非目标能力

`Litex.Fn domain codomain` 允许任意 host 类型上、带 `Litex.In` 证明的调用。
若将来要证明两个任意异构表示 `x` 和 `y` 语义相同时一定有
`f.call x hx = f.call y hy`，仍需要一项跨所有函数的 ABI 契约。本 adapter 没有
使用这项更强声明，因此它不是当前 showcase 的剩余缺口。

## 与“柯西列由实数完备性收敛”的边界

上面的结论只针对当前“收敛数列乘常数”源文件：它还需要的
ToLean 功能数量是 **0**。它已经覆盖 concrete predicate、匿名函数、
局部 `forall` claim、存在量词的 `obtain`/`witness`、嵌套证明、
`by def` 以及绝对值和有序字段运算的 Result 回放。

以后若要把“柯西列必收敛”从一般实数完备性完整编译到 Lean，
则是另一层任务。当前已支持在定理证明中写
`have E power_set(R) = {x R: ...}` 这类局部有类型集合定义；
现在，前两项通用基础能力已经打通：

- Example 67 可以在命名定理的局部证明中调用一般的
  `real_least_upper_bound_exists(S, upper)`。编译器读取的是 Result 中的
  builtin 定理 ID、按序前提检查和结论 FactId；
- Example 68 可以先写 `have E power_set(R) = {x R: ...}`，再证明
  `x $in E`。这条路径复用通用的透明定义约简，精确引用定义等式的
  FactId，并没有增加集合名或题目名特化。

因此，继续推“柯西列由实数完备性收敛”时，目前还剩两个主要的通用表示缺口：

1. `x <= 0` 或字面单点集成员等符号证据，与 LUB 所需的精确实数次序观察尚未共用
   同一个表示；
2. `exist q Q` 一类 typed existential 还需要保留同一个原生
   `q : ℚ` 见证，否则 Mathlib 构造的见证与当前异构 wrapper 选出的
   代表元无法保证相同。

这两项不是当前 `main.lit` 的隐藏依赖，也不应通过柯西列、
有理数稠密性或某个定理名的特化分支解决。

## 核验证据

- Litex strict runner：成功，退出码 `0`；
- 生成文件 Lean kernel gate：成功，退出码 `0`；
- Mathlib adapter：`lake build LitexToMathlib` 成功；
- 编译器单元合约：151/151 通过；tracer：76/76 通过；
  CLI：4/4 通过；binary 测试：2/2 通过；
- 生成账本：67 对文件重生成后无漂移，并全部通过真实 Lean kernel；
- real-sequence 定义与 implicit-binder tracer 已包含在完整生成账本中；
- 同构改名测试已包含在 76 个 tracer 中；
- 禁止项扫描：当前源文件、生成文件和 adapter 无
  `axiom`/`trust`/`sorry`/`admit`。

Lean 对生成文件仍报告若干“未使用 simp 参数”和“tactic 可简化”的 warning。
这是之后可单独做的生成代码精简，不影响当前 Lean kernel 验证。

## 非目标／信任边界

- 没有新增“收敛数列乘常数仍收敛”的 kernel builtin；
- 没有按 `is_eventually_close`、`converges_to` 或
  `converges_to_mul_const` 的名字分支；
- 没有匹配整份源文本或本例 AST；
- 没有将 Result 的诊断文字重新解析成证明；
- 没有使用项目公理、信任声明或证明洞。
- 没有声称或假设任意异构输入之间的函数表示不变性。
