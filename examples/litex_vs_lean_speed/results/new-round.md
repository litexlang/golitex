| 领域 | 用例 | 表达：Litex 德布鲁因因子 DF* ↓ | 表达：Lean 德布鲁因因子 DF* ↓ | 速度：Litex 耗时 (ms) ↓ | 速度：Lean 耗时 (ms) ↓ | 速度：Litex 加速比（Lean 耗时÷Litex 耗时）↑ | Lean 最快路线 | 源码 |
| --- | --- | ---: | ---: | ---: | ---: | ---: | --- | --- |
| 经典大证明 | sqrt(2) 不是有理数 | 1.73 | 4.91 | 199.285 | 779.754 | **3.91×** | `scratch` | [litex](../sources/new-round/sqrt_two_irrational.lit) · [lean](../sources/new-round/sqrt_two_irrational__scratch.lean) |
| 集合 | 并交分配律 | 1.08 | 1.09 | 0.286 | 1.380 | **4.83×** | `lemma` | [litex](../sources/new-round/set_union_inter_distrib.lit) · [lean](../sources/new-round/set_union_inter_distrib__lemma.lean) |
| 集合 | 差集对并集的德摩根律 | 0.85 | 1.16 | 0.279 | 22.842 | **81.96×** | `ext_simp` | [litex](../sources/new-round/set_diff_union.lit) · [lean](../sources/new-round/set_diff_union__ext_simp.lean) |
| 集合 | 交集保持包含 | 0.99 | 1.00 | 0.934 | 1.500 | **1.61×** | `lemma` | [litex](../sources/new-round/set_inter_monotone.lit) · [lean](../sources/new-round/set_inter_monotone__lemma.lean) |
| 函数 | 函数值属于值域 | 0.68 | 1.36 | 0.313 | 0.920 | **2.94×** | `lemma` | [litex](../sources/new-round/function_mem_range.lit) · [lean](../sources/new-round/function_mem_range__lemma.lean) |
| 整数算术 | 整数除法的商余分解 | 0.35 | 1.24 | 1.135 | 3.341 | **2.94×** | `lemma` | [litex](../sources/new-round/integer_division_decomposition.lit) · [lean](../sources/new-round/integer_division_decomposition__lemma.lean) |
| 整除 | 整数乘积被其因子整除 | 0.52 | 1.24 | 0.604 | 1.712 | **2.83×** | `lemma` | [litex](../sources/new-round/integer_divisibility.lit) · [lean](../sources/new-round/integer_divisibility__lemma.lean) |
| 有限组合 | 集合 {1,2,3} 的元素个数 | 0.44 | 0.75 | 0.049 | 3.597 | **73.43×** | `decide` | [litex](../sources/new-round/finite_cardinality.lit) · [lean](../sources/new-round/finite_cardinality__decide.lean) |
| 有限组合 | n 元集合有 2^n 个子集 | 0.84 | 0.78 | 0.250 | 1.047 | **4.19×** | `lemma` | [litex](../sources/new-round/powerset_cardinality.lit) · [lean](../sources/new-round/powerset_cardinality__lemma.lean) |
| 组合 | 自然数阶乘为正 | 0.42 | 0.98 | 0.165 | 0.582 | **3.54×** | `lemma` | [litex](../sources/new-round/factorial_positive.lit) · [lean](../sources/new-round/factorial_positive__lemma.lean) |
| 微积分 | x^2 在 3 处的导数为 6 | 0.80 | 3.07 | 1.555 | 46.258 | **29.75×** | `chain` | [litex](../sources/new-round/derivative_square_at_three.lit) · [lean](../sources/new-round/derivative_square_at_three__chain.lean) |
| 笛卡尔积 | 有序对的坐标重构 | 0.35 | 0.67 | 0.170 | 0.567 | **3.34×** | `lemma` | [litex](../sources/new-round/pair_reconstruction.lit) · [lean](../sources/new-round/pair_reconstruction__lemma.lean) |
| 微积分 | x^2 在 3 处连续 | 0.59 | 1.14 | 0.377 | 8.986 | **23.83×** | `lemma` | [litex](../sources/new-round/continuity_square_at_three.lit) · [lean](../sources/new-round/continuity_square_at_three__lemma.lean) |

**表达长度**：德布鲁因因子 DF* = 该语言有效字符数 ÷ 同题普通数学有效字符数，越小越简短。**运行速度**：耗时单位为毫秒；Litex 加速比 = Lean 耗时 ÷ Litex 耗时，越大表示 Litex 越快。这是共享英文数学文本的回溯示例，非预先选定原文的翻译实验；— 表示缺少基线或源码与计时用例定义不一致。[原文、口径与限制](../README.md#de-bruijn-factor)。
