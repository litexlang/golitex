# 收敛数列乘常数：Litex → Lean → Mathlib

这个 showcase 使用一个完整的分析学例子：

1. `is_eventually_close` 表示数列从某个自然数位置开始，始终落在给定误差内；
2. `converges_to` 表示对每个正实数误差，都存在这样的起点；
3. `converges_to_mul_const` 证明：若 `s` 收敛到 `a`，则 `n ↦ c * s(n)` 收敛到 `c * a`。

证明把原数列的误差取为
`epsilon / (abs(c) + 1)`。分母始终为正，因此无须对 `c = 0`
分情况；然后利用绝对值的乘法公式和不等式链把新误差压到
`epsilon` 以下。

## 当前结果

| 层 | 状态 | 证据 |
| --- | --- | --- |
| Litex 源文件 | 通过 | strict isolated runner 退出码 `0`，顶层 `ok: true` |
| StmtResult → Lean | 通过 | 直接编译当前 `main.lit`，产生新的 `LitexGenerate.lean` |
| Lean kernel | 通过 | `lake env lean .../LitexGenerate.lean` 退出码 `0` |
| Mathlib 消费层 | 通过 | `lake build LitexToMathlib` 成功，adapter 实际调用生成的 `converges_to_mul_const` |
| 通用回归 | 通过 | 通用生成样例经过重新生成、确定性比对和真实 Lean kernel 检查 |

`main.lit`、生成文件和 adapter 都不含 `axiom`、`trust`、`sorry`
或 `admit`。编译器也不再按这个定理的名字、整份源文本或特定 AST
分支。

## 三个文件的边界

| 文件 | 所有者 | 角色 |
| --- | --- | --- |
| `main.lit` | Litex 作者 | 数学定义和证明的唯一源文件 |
| `LitexGenerate.lean` | ToLean 编译器 | 完全由 StmtResult 生成，禁止手改 |
| `LitexToMathlib.lean` | adapter 作者 | 引用生成定理，将结论导出为 Mathlib `Filter.Tendsto` |

## 当前边界

当前 adapter 已经把 Litex 数列限制在精确的自然数输入上：
`toMathlibSequence s n` 直接用 `n : ℕ` 及
`Litex.In.own Litex.N n` 调用生成函数。因此 Mathlib 结论的索引类型已经是
普通的 `ℕ → ℝ`，不再需要用户操作额外的 `NaturalInput`。

`Litex.Fn` 仍然支持其他 host 类型上、带 membership 证明的异构调用。
当前导出并没有声称两种任意异构表示会给出相同函数值；这种更强的
函数表示不变性仍然是 ABI 的非目标能力，但它不是本 showcase 导出
原生 Mathlib 数列的阻塞。完整审计见
[`TOLEAN_AUDIT.md`](TOLEAN_AUDIT.md)。

## 复现

从仓库根目录运行：

```bash
target/release/litex -compact -strict -runner -isolated \
  -f showcases/litex_to_lean_mathlib_pipeline/showcase2/main.lit

target/release/stmt_result_to_lean_compiler compile \
  showcases/litex_to_lean_mathlib_pipeline/showcase2/main.lit \
  showcases/litex_to_lean_mathlib_pipeline/showcase2/LitexGenerate.lean

cargo test --release --test stmt_result_to_lean_compiler_tracers

cd lean
lake env lean \
  ../showcases/litex_to_lean_mathlib_pipeline/showcase2/LitexGenerate.lean
lake build LitexToMathlib
```

Lean 会对生成证明给出一些 tactic/linter 建议，但没有错误；这些是生成代码
长度和清理质量问题，不是信任或核验缺口。
