| 领域 | 用例 | Litex (ms) | Lean (ms) | Lean÷Litex | Lean 最快路线 | 源码 |
| --- | --- | ---: | ---: | ---: | --- | --- |
| 谓词定义 + 见证 | 自定义奇数谓词并见证 7 为奇数 | 0.521 | 4.575 | **8.77×** | `term` | [litex](../sources/statement-forms/prop_definition_witness.lit) · [lean](../sources/statement-forms/prop_definition_witness__term.lean) |
| 自定义谓词推理 | 奇数乘以 3 加 2 仍是奇数 | 6.810 | 36.353 | **5.34×** | `rcases_omega` | [litex](../sources/statement-forms/odd_shift.lit) · [lean](../sources/statement-forms/odd_shift__rcases_omega.lean) |
| 极限风格（ε-N） | 互反序列 1/n 可以任意小 | 9.553 | 35.269 | **3.69×** | `archimedean` | [litex](../sources/statement-forms/reciprocal_tends_to_zero.lit) · [lean](../sources/statement-forms/reciprocal_tends_to_zero__archimedean.lean) |
| 集合相等的义务 | 包含于 B 的集合与 B 的并等于 B | 0.186 | 1.217 | **6.53×** | `lemma` | [litex](../sources/statement-forms/set_union_subset_eq.lit) · [lean](../sources/statement-forms/set_union_subset_eq__lemma.lean) |
