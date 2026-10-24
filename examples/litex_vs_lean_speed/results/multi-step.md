| 领域 | 用例 | Litex (ms) | Lean (ms) | Lean÷Litex | Lean 最快路线 | 源码 |
| --- | --- | ---: | ---: | ---: | --- | --- |
| 不等式 | 平方和为零则两数都为零 | 0.685 | 209.744 | **306.11×** | `nlinarith` | [litex](../sources/multi-step/sum_sq_zero.lit) · [lean](../sources/multi-step/sum_sq_zero__nlinarith.lean) |
| 不等式 | 正数的 x/(x+1) 为正 | 0.949 | 29.170 | **30.75×** | `div_pos` | [litex](../sources/multi-step/positive_ratio.lit) · [lean](../sources/multi-step/positive_ratio__div_pos.lean) |
| 代数 | 等式两边同乘 2 的消去 | 0.335 | 10.726 | **32.01×** | `cancel` | [litex](../sources/multi-step/mul_cancel.lit) · [lean](../sources/multi-step/mul_cancel__cancel.lean) |
| 不等式 | 实数的平方加一为正 | 2.189 | 17.404 | **7.95×** | `positivity` | [litex](../sources/multi-step/sq_plus_one_pos.lit) · [lean](../sources/multi-step/sq_plus_one_pos__positivity.lean) |
| 不等式 | x²+y² ≥ 2xy | 52.271 | 87.954 | **1.68×** | `nlinarith` | [litex](../sources/multi-step/sum_sq_ge_two_mul.lit) · [lean](../sources/multi-step/sum_sq_ge_two_mul__nlinarith.lean) |
| 存在构造 | 任意正整数之上都有偶数 | 4.426 | 34.877 | **7.88×** | `witness` | [litex](../sources/multi-step/even_witness_above.lit) · [lean](../sources/multi-step/even_witness_above__witness.lean) |
| 算术 | 正整数小于它的两倍 | 0.885 | 14.761 | **16.69×** | `omega` | [litex](../sources/multi-step/nat_succ_lt_two_mul.lit) · [lean](../sources/multi-step/nat_succ_lt_two_mul__omega.lean) |
