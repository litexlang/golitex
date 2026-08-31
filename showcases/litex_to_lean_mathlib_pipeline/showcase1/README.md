# 从 `by sorry` 到原生 Lean 定理

这个 showcase 只讲一条主线：先在 Lean 里写下想证明的目标，再用
Litex 完成数学证明，把 Litex 编译成 Lean，最后在一个短小的 Lean
证明里引用生成定理。最终 theorem 的 statement 必须完全不知道
Litex 存在；`Litex.*` 和 generated names 只允许出现在 `:= by` 之后。

贯穿全流程的命题是：前 `n` 个正奇数之和等于 `n²`。

```text
1 + 3 + 5 + ⋯ + (2n - 1) = n²
```

## 先看清楚每个文件

```text
showcase1/
├── README.md               # 你正在读的流程说明
├── main.lit                # 1. Litex 数学与证明；唯一源文件
├── Generated.lean          # 2. 编译器生成；禁止手改
├── Adapter.lean            # 3. 真实 cite 生成定理并整理接口
├── Final.lean              # 4. 原生 Final 目标；等待已证明的 bridge
├── litex.config            # Litex 文件顺序
├── lakefile.toml           # 本目录自己的 Lean/Lake 工程入口
├── lake-manifest.json      # 本地 path dependency 与 Mathlib 版本锁定
├── lean-toolchain          # 固定使用 Lean 4.31.0
└── extras/
    ├── property_flow.lit   # 独立的 prop 生命周期实验，不属于主流程
    ├── compiler_gaps.md    # 上述实验尚缺的编译器 consumer
    └── litex.config        # extras 子模块自己的导出顺序
```

`math_collections.md` 和 `natural_mathematics.md` 已删除；本例的数学、接口、
运行方法和诚实边界统一放在这一份 README 中。原来只做二次 import 的
聚合 `.lean` 文件也已删除。

## Pipeline 总览

```text
脑中的 Lean 目标（暂时 by sorry）
                ↓
main.lit：用 Litex 写出并检查数学证明
                ↓ stmt_result_to_lean_compiler
Generated.lean：生成可由 Lean kernel 检查的定理
                ↓ import + cite
Adapter.lean：cite 生成定理，并原型化 Same → Eq 证书
                ↓ 等 Core 提供已证明的证书
Final.lean：声明完全原生的 theorem
```

关键纪律是：`Generated.lean` 只能由编译器重生成；手写的接口整理必须
放在 `Adapter.lean`；最终使用必须放在 `Final.lean`。在原生消元
bridge 真正被证明之前，`Final.lean` 不得用公理、proof hole 或独立重证
伪装成已打通。

## 第 0 步：先在 Lean 里写目标

假设你会写 Lean 的定理框架，但不会中间的归纳证明。最初可以先构思成：

```lean
import Adapter

namespace OddSumPipeline

theorem firstHundredPositiveOddIntegersSum :
    ∑ k ∈ Finset.Icc (1 : ℤ) 100, (2 * k - 1) = 10000 := by
  sorry

end OddSumPipeline
```

这里的 `sorry` 只用于说明“开始时缺的洞”。注意 theorem statement
只包含 `Finset.Icc`、`ℤ`、求和与 Lean `=`：它不应该出现 `Litex.Same`、
`Litex.sum`、`__Compiler_main.*` 或 Adapter 自己的 wrapper。

## 第 1 步：在 Litex 里完成数学

[`main.lit`](main.lit) 先定义第 `k` 个正奇数：

```litex
have fn kth_odd(k Z) Z = 2 * k - 1
```

然后从 `1` 做整数归纳：

- 基础步：`sum(1, 1, kth_odd) = 1 = 1²`；
- 归纳步：把最后一项 `2(n + 1) - 1` 拆出来；
- 使用归纳假设后，计算
  `n² + (2(n + 1) - 1) = (n + 1)²`。

对应的核心 Litex 代码是：

```litex
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

这一步解决的是数学，不是把 Lean tactic 逐行翻译成 Litex。

## 第 2 步：把 Litex 编译成 Lean

编译器从 `main.lit` 的已检查 statement results 生成
[`Generated.lean`](Generated.lean)。主定理的公开形状是：

```lean
__Compiler_main.sum_first_odds :
  ∀ (n : ℤ) (_ : Litex.Le (1 : ℂ) (n : ℂ)),
    Litex.Same
      (Litex.sum (1 : ℤ) n __Compiler_main.kth_odd)
      ((((n : ℚ) ^ (2 : ℤ) : ℚ) : ℂ))
```

生成文件可能很长，因为它重放 Litex verifier 已经选中的证据路径。下游
不需要读完它，更不应该手改它；只要 import 并使用公开定理即可。

## 第 3 步：adapter 必须真的 cite，再消成原生 `Eq`

[`Adapter.lean`](Adapter.lean) 首先把普通 Lean 前提 `(1 : ℤ) ≤ n` 转成生成
定理需要的 `Litex.Le`，然后定义一个局部、待审核的消元证书：

真正关键的调用是：

```lean
structure IntegerSameEqBridge : Prop where
  toEq {left right : ℤ} :
    Litex.Same left (right : ℂ) → left = right
```

这个 structure 没有定义任何 inhabitant，也不是把 `Equal` 重新定义成
`Same`。它要求 Core 最终提供一个真正的 Lean 证明：对于整数值语义等式，
`Same left (right : ℂ)` 能安全消成 `left = right`。

Adapter 中的 `sumFirstOddsNative` 已由 Lean 4.31 检查。它的 conclusion 是普通
Mathlib 命题：

```lean
theorem sumFirstOddsNative
    (bridge : IntegerSameEqBridge)
    (n : ℤ)
    (oneLeN : (1 : ℤ) ≤ n) :
    ∑ k ∈ Finset.Icc (1 : ℤ) n, (2 * k - 1) = n ^ 2 := by
  have generated := __Compiler_main.sum_first_odds n …
  …
  have exactCarrierEq := bridge.toEq exactCarrierSame
  simpa [Litex.sum, Litex.integerRangeSum, __Compiler_main.kth_odd] using
    exactCarrierEq
```

这里 generated theorem 是 live dependency：删掉 `generated` 或 `exactCarrierSame` 就无法构造
`exactCarrierEq`。Adapter 没有重写 odd-sum 归纳。

## 第 4 步：bridge 证明后，再关闭 Final

[`Final.lean`](Final.lean) 现在只保留原生目标规格，还没有声明一个无条件
theorem。原因很具体：`IntegerSameEqBridge` 的类型和条件性使用已经通过，
但该证书尚未在 Core 中被构造。

```lean
theorem firstHundredPositiveOddIntegersSum :
    ∑ k ∈ Finset.Icc (1 : ℤ) 100, (2 * k - 1) = 10000 := by
  exact OddSumPipeline.sumFirstOddsNative
    Litex.integerSameEqBridge 100 (by norm_num)
```

上面是 bridge 被证明并命名后的最终形状，不是当前可执行代码。特别注意：
statement 完全不知道 Litex 存在；只有 `by` 之后的 proof 会经由 Adapter
间接使用 generated theorem。

## 解决编辑器里的 `unknown module prefix`

原先的 `lakefile.toml` 只在兄弟目录 `lean/` 中。你从 `showcase1` 点击
`.lean` 文件时，Lean 4 extension 向父目录找不到 Lake 工程，于是直接启动
裸 Lean；裸 Lean 的搜索路径只有工具链自己的 `lib/lean`，当然找不到
`LitexToMathlibPipelineGenerated`。

本目录现在有自己的 [`lakefile.toml`](lakefile.toml) 和
[`lean-toolchain`](lean-toolchain)：

- 固定使用你电脑上的 `leanprover/lean4:v4.31.0`；
- 通过本地 path dependency 使用仓库的 `lean/` 包；
- 复用 `lean/.lake/packages` 里的 Mathlib dependency checkout；
- 把 `Generated`、`Adapter`、`Final` 注册为真正的 Lean modules。

第一次使用，在终端执行：

```bash
cd /Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/showcases/litex_to_lean_mathlib_pipeline/showcase1
lake build
```

然后在编辑器里重新打开 `.lean` 文件，或执行 `Lean 4: Restart File`。如果
扩展仍缓存旧工程，使用 `Lean 4: Project: Open Local Project…` 打开这个
`showcase1` 文件夹。不要直接运行裸 `lean Final.lean`；命令行也应使用
`lake env lean Final.lean`。

## 从仓库根目录复现整条链

```bash
cargo build --release

target/release/litex -compact -strict -summarize \
  -f showcases/litex_to_lean_mathlib_pipeline/showcase1/main.lit

target/release/stmt_result_to_lean_compiler compile \
  showcases/litex_to_lean_mathlib_pipeline/showcase1/main.lit \
  showcases/litex_to_lean_mathlib_pipeline/showcase1/Generated.lean

cargo test --release --test stmt_result_to_lean_compiler_tracers \
  litex_to_mathlib_pipeline_showcase_generated_lean_has_not_drifted

cd showcases/litex_to_lean_mathlib_pipeline/showcase1
lake env lean Generated.lean
lake env lean Adapter.lean
lake env lean Final.lean
lake build
```

Litex 命令必须退出 `0`，且末尾 run summary 的 `result` 必须为
`success`；drift test 要求重新生成的 Lean 与 checked-in
`Generated.lean` 完全一致；最后四个 Lake 命令必须由真实 Lean kernel
接受。当前 CLI 已不接受旧的 `-runner` 组合。

## 当前诚实边界

当前 generated theorem 的结论是异构语义等式 `Litex.Same`。它已经能在
Lean 中被引用和组合，但当前公共 Core 还没有一个已证明的 eliminator，
把这一特定的 `Litex.Same (integer sum) (complex square)` 直接消成普通
Mathlib 整数等式：

```lean
∑ k ∈ Finset.Icc (1 : ℤ) n, (2 * k - 1) = n ^ 2
```

因此，本 showcase 目前已检查的是两层：

- 无条件的 `Litex → generated Lean → Litex.Same`；
- 以 `IntegerSameEqBridge` 证书为显式前提的
  `generated Lean → 原生 Finset 等式`。

第二层的 Adapter proof 已通过 Lean kernel，但 bridge 证书本身尚未实现，
所以无条件 Final theorem 仍未声明。以前的 adapter 虽然 import 了 generated
module，却独立写了一遍 `Int.leInduction`；那不能证明 generated theorem
被复用，所以已经移除。

下一步不是再写一份归纳，而是审核 `IntegerSameEqBridge.toEq`
这个精确接口，然后在 Core 内部使用封闭的 `Same` 构造子给出 sound proof，
或让 compiler 从 verifier evidence 直接生成等价证书。这个缺口不能用
`axiom`、`sorry`、`admit`、未使用的 generated 假设或独立重证掩盖。

`extras/property_flow.lit` 还演示了
`prop definition → reusable law → instance → composition`，但其若干局部
predicate result consumers 尚未被 ToLean 支持。它的准确错误、期望行为和
验收命令记录在 `extras/compiler_gaps.md`；它不属于上面的已打通主链。
