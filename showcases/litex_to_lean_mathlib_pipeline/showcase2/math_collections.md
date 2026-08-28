# Mathematical collection：收敛数列乘常数

## Litex 接口

| 声明 | 数学含义 | 依赖 |
| --- | --- | --- |
| `is_eventually_close(s, a, epsilon, N0)` | 对每个 `n >= N0`，都有 `abs(s(n) - a) < epsilon` | `N`、`R`、绝对值与顺序 |
| `converges_to(s, a)` | 对每个正实数 `epsilon`，都存在一个自然数起点，使 `s` 最终接近 `a` | `is_eventually_close` |
| `converges_to_mul_const` | 若 `s` 收敛到 `a`，则 `n ↦ c * s(n)` 收敛到 `c * a` | 实数乘法、绝对值乘法公式与顺序 |

这里的数列类型直接写作 `fn(n N) R`，起点属于 `N`。证明使用
`epsilon / (abs(c) + 1)`；因为分母严格为正，这个选择同时覆盖 `c = 0`
和 `c != 0`。

## 证明依赖图

```text
converges_to(s, a)
  → 对 epsilon / (abs(c)+1) 取得 N0
  → n >= N0 时取得 abs(s(n)-a) < epsilon / (abs(c)+1)
  → abs(c*(s(n)-a)) = abs(c) * abs(s(n)-a)
  → 新误差 < epsilon
  → is_eventually_close(n ↦ c*s(n), c*a, epsilon, N0)
  → converges_to(n ↦ c*s(n), c*a)
```

## Lean 表示

- `is_eventually_close` 和 `converges_to` 由 ToLean 作为具体 `def` 生成；
- `converges_to_mul_const` 由 ToLean 作为有证明体的 `theorem` 生成；
- `R+` 使用 Lean 的精确正实数 subtype carrier；
- 存在量词的 witness 与 membership 证明分别保留；
- 异构表示变换通过 `Litex.Same` 和 `Litex.In.congr` 显式进行。

## Mathlib 导出

`LitexToMathlib.lean` 把 `s : Litex.Fn Litex.N Litex.R` 限制为原生数列
`ℕ → ℝ`：对 `n : ℕ` 直接提供 `Litex.In.own Litex.N n`。它将生成的
`converges_to` 导出为 `Filter.Tendsto ... atTop (nhds a)`。最终定理
`tendsto_mul_const_from_generated` 直接调用生成的
`__Compiler_main.converges_to_mul_const`，而不是在 Mathlib 中独立重证。

这个限制不要求任意异构自然数表示的函数值相等；那是更强的
全局函数 ABI 契约，不是当前 `ℕ → ℝ` 导出的前提。

## 信任边界

- source `axiom`：无；
- source `trust`：无；
- sequence-specific builtin theorem：无；
- “乘常数保持收敛”kernel theorem：无；
- 生成 Lean 中的 `axiom`/`sorry`/`admit`：无；
- 生成文件由编译器写入，adapter 是独立手写消费层；
- Litex strict runner、Lean kernel 和 Mathlib build 均已通过。
