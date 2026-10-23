| 领域 | 用例 | Litex (ms) | Lean (ms) | Lean÷Litex | Lean 最快路线 | 源码 |
| --- | --- | ---: | ---: | ---: | --- | --- |
| 经典大证明 | sqrt(2) 不是有理数 | 25.554 | 750.544 | **29.37×** | `scratch` | [litex](../sources/new-round/sqrt_two_irrational.lit) · [lean](../sources/new-round/sqrt_two_irrational__scratch.lean) |
| 集合 | 并交分配律 | 0.234 | 1.348 | **5.77×** | `lemma` | [litex](../sources/new-round/set_union_inter_distrib.lit) · [lean](../sources/new-round/set_union_inter_distrib__lemma.lean) |
| 集合 | 差集对并集的德摩根律 | 0.221 | 21.592 | **97.48×** | `ext_simp` | [litex](../sources/new-round/set_diff_union.lit) · [lean](../sources/new-round/set_diff_union__ext_simp.lean) |
| 集合 | 交集保持包含 | 0.286 | 1.355 | **4.73×** | `lemma` | [litex](../sources/new-round/set_inter_monotone.lit) · [lean](../sources/new-round/set_inter_monotone__lemma.lean) |
| 函数 | 函数值属于值域 | 0.228 | 0.861 | **3.78×** | `lemma` | [litex](../sources/new-round/function_mem_range.lit) · [lean](../sources/new-round/function_mem_range__lemma.lean) |
| 函数 | 复合的结合律 | 6.454 | 0.879 | **0.14×** | `lemma` | [litex](../sources/new-round/function_comp_assoc.lit) · [lean](../sources/new-round/function_comp_assoc__lemma.lean) |
| 整数算术 | 整数除法的商余分解 | 0.379 | 3.183 | **8.41×** | `lemma` | [litex](../sources/new-round/integer_division_decomposition.lit) · [lean](../sources/new-round/integer_division_decomposition__lemma.lean) |
| 整除 | 整数乘积被其因子整除 | 0.204 | 1.719 | **8.42×** | `lemma` | [litex](../sources/new-round/integer_divisibility.lit) · [lean](../sources/new-round/integer_divisibility__lemma.lean) |
| 有限组合 | 集合 {1,2,3} 的元素个数 | 0.062 | 3.754 | **60.91×** | `decide` | [litex](../sources/new-round/finite_cardinality.lit) · [lean](../sources/new-round/finite_cardinality__decide.lean) |
| 有限组合 | n 元集合有 2^n 个子集 | 0.165 | 1.083 | **6.56×** | `lemma` | [litex](../sources/new-round/powerset_cardinality.lit) · [lean](../sources/new-round/powerset_cardinality__lemma.lean) |
| 组合 | 自然数阶乘为正 | 0.096 | 0.597 | **6.25×** | `lemma` | [litex](../sources/new-round/factorial_positive.lit) · [lean](../sources/new-round/factorial_positive__lemma.lean) |
| 微积分 | x^2 在 3 处的导数为 6 | 0.850 | 49.035 | **57.67×** | `chain` | [litex](../sources/new-round/derivative_square_at_three.lit) · [lean](../sources/new-round/derivative_square_at_three__chain.lean) |
| 笛卡尔积 | 有序对的坐标重构 | 0.195 | 0.608 | **3.12×** | `lemma` | [litex](../sources/new-round/pair_reconstruction.lit) · [lean](../sources/new-round/pair_reconstruction__lemma.lean) |
| 微积分 | x^2 在 3 处连续 | 0.250 | 8.686 | **34.79×** | `lemma` | [litex](../sources/new-round/continuity_square_at_three.lit) · [lean](../sources/new-round/continuity_square_at_three__lemma.lean) |
