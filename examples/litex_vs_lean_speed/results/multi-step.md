| 领域 | 用例 | 表达：Litex 德布鲁因因子 DF* ↓ | 表达：Lean 德布鲁因因子 DF* ↓ | 速度：Litex 耗时 (ms) ↓ | 速度：Lean 耗时 (ms) ↓ | 速度：Litex 加速比（Lean 耗时÷Litex 耗时）↑ | Lean 最快路线 | 源码 |
| --- | --- | ---: | ---: | ---: | ---: | ---: | --- | --- |
| 不等式 | 平方和为零则两数都为零 | 0.42 | 1.19 | 0.685 | 209.744 | **306.11×** | `nlinarith` | [litex](../sources/multi-step/sum_sq_zero.lit) · [lean](../sources/multi-step/sum_sq_zero__nlinarith.lean) |
| 不等式 | 正数的 x/(x+1) 为正 | 0.37 | 1.11 | 0.949 | 29.170 | **30.75×** | `div_pos` | [litex](../sources/multi-step/positive_ratio.lit) · [lean](../sources/multi-step/positive_ratio__div_pos.lean) |
| 代数 | 等式两边同乘 2 的消去 | 0.43 | 1.54 | 0.335 | 10.726 | **32.01×** | `cancel` | [litex](../sources/multi-step/mul_cancel.lit) · [lean](../sources/multi-step/mul_cancel__cancel.lean) |
| 不等式 | 实数的平方加一为正 | 0.39 | 1.07 | 2.189 | 17.404 | **7.95×** | `positivity` | [litex](../sources/multi-step/sq_plus_one_pos.lit) · [lean](../sources/multi-step/sq_plus_one_pos__positivity.lean) |
| 不等式 | x²+y² ≥ 2xy | 1.02 | 1.34 | 52.271 | 87.954 | **1.68×** | `nlinarith` | [litex](../sources/multi-step/sum_sq_ge_two_mul.lit) · [lean](../sources/multi-step/sum_sq_ge_two_mul__nlinarith.lean) |
| 存在构造 | 任意正整数之上都有偶数 | — | — | 4.426 | 34.877 | **7.88×** | `witness` | [litex](../sources/multi-step/even_witness_above.lit) · [lean](../sources/multi-step/even_witness_above__witness.lean) |
| 算术 | 正整数小于它的两倍 | — | — | 0.885 | 14.761 | **16.69×** | `omega` | [litex](../sources/multi-step/nat_succ_lt_two_mul.lit) · [lean](../sources/multi-step/nat_succ_lt_two_mul__omega.lean) |

**表达长度**：德布鲁因因子 DF* = 该语言有效字符数 ÷ 同题普通数学有效字符数，越小越简短。**运行速度**：耗时单位为毫秒；Litex 加速比 = Lean 耗时 ÷ Litex 耗时，越大表示 Litex 越快。这是共享英文数学文本的回溯示例，非预先选定原文的翻译实验；— 表示缺少基线或源码与计时用例定义不一致。[原文、口径与限制](../README.md#de-bruijn-factor)。
