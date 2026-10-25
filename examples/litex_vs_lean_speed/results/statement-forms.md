| 领域 | 用例 | 表达：Litex 德布鲁因因子 DF* ↓ | 表达：Lean 德布鲁因因子 DF* ↓ | 速度：Litex 耗时 (ms) ↓ | 速度：Lean 耗时 (ms) ↓ | 速度：Litex 加速比（Lean 耗时÷Litex 耗时）↑ | Lean 最快路线 | 源码 |
| --- | --- | ---: | ---: | ---: | ---: | ---: | --- | --- |
| 谓词定义 + 见证 | 自定义奇数谓词并见证 7 为奇数 | 0.70 | 0.63 | 0.521 | 4.575 | **8.77×** | `term` | [litex](../sources/statement-forms/prop_definition_witness.lit) · [lean](../sources/statement-forms/prop_definition_witness__term.lean) |
| 自定义谓词推理 | 奇数乘以 3 加 2 仍是奇数 | 1.14 | 0.70 | 6.810 | 36.353 | **5.34×** | `rcases_omega` | [litex](../sources/statement-forms/odd_shift.lit) · [lean](../sources/statement-forms/odd_shift__rcases_omega.lean) |
| 极限风格（ε-N） | 互反序列 1/n 可以任意小 | 1.29 | 0.95 | 9.553 | 35.269 | **3.69×** | `archimedean` | [litex](../sources/statement-forms/reciprocal_tends_to_zero.lit) · [lean](../sources/statement-forms/reciprocal_tends_to_zero__archimedean.lean) |
| 集合相等的义务 | 包含于 B 的集合与 B 的并等于 B | 0.46 | 0.63 | 0.186 | 1.217 | **6.53×** | `lemma` | [litex](../sources/statement-forms/set_union_subset_eq.lit) · [lean](../sources/statement-forms/set_union_subset_eq__lemma.lean) |

**表达长度**：德布鲁因因子 DF* = 该语言有效字符数 ÷ 同题普通数学有效字符数，越小越简短。**运行速度**：耗时单位为毫秒；Litex 加速比 = Lean 耗时 ÷ Litex 耗时，越大表示 Litex 越快。这是共享英文数学文本的回溯示例，非预先选定原文的翻译实验；— 表示缺少基线或源码与计时用例定义不一致。[原文、口径与限制](../README.md#de-bruijn-factor)。
