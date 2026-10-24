# sources

每一条用例的 Litex 与 Lean 源码，按批次和领域分组。所有 `.lit` 文件都用 release 的
`target/release/litex -f` 独立跑过，`run_result` 为 `success`。

| 目录 | 内容 | 来源批次 |
| --- | --- | --- |
| `arithmetic/` | 自然数加法、实数平方根 | 2026-10-22 基础算术与根式 |
| `sums/` | 区间求和、有限集合求和、三角具体值与恒等式 | 2026-10-22 有限求和与三角 |
| `elementary/` | 素性、最大公因数、阶乘、大数四次方恒等式、对数、根式乘 | 2026-10-22 初等计算与数论 |
| `quantifiers/` | 全称、见证、唯一存在、存在消去（21 例，多个 Lean 路线） | 2026-10-23 量词批次 |
| `declarations/` | 函数、谓词、分段、递归、结构、命名定理、反证、分类、归纳 | 2026-10-23 定义与证明命令批次 |
| `new-round/` | 集合、函数、整数算术、整除、有限组合、微积分、笛卡尔积、√2 无理 | 2026-10-23 本目录新增 |
| `multi-step/` | 不等式、代数消去、数论整除、存在构造、算术（Lean 无同形定理，必须自己推） | 2026-10-23 第二轮 |
| `statement-forms/` | 谓词定义 + 见证、从谓词取见证、ε-N 极限小问题、集合相等义务 | 2026-10-23 第三轮 |
| `type-bridge/` | 同一 Lean 命题的转换标注/桥接自动化/直接引理对照，及两条对应 Litex 算术语句 | 2026-10-24 类型桥接分项实验 |
| `quantitative-iteration/` | 参数化 Newton、二次函数梯度下降、含扰动几何递推；含完整双版本源码与数学设计 | 2026-10-24，完整进程口径 |
| `lean-proof-pipeline/` | `1 + 1 = 2` 与参数化加一的真实 Lean 证明项、显式参数和原始 `Expr` | 2026-10-24，解释实验，无计时 |
| `search-expansion/` | 16/64/128 项求和平移；0/12/24 条无关假设的平方差不等式；保留全部速度方向和直接 Lean 基线 | 2026-10-24，独立检查路径批次 |

命名约定：

- `<case>.lit`：Litex 源码，一例一个文件。
- `<case>_<method>.lean` 或 `<case>__<method>.lean`：同一命题的一条 Lean 证明路线；
  批次之间的分隔符不同（`_` 与 `__`），保持与各自批次记录一致。
- `new-round/Repeat.lean`、`new-round/Validate.lean`、`multi-step/Repeat.lean`、`multi-step/Validate.lean`：本目录计时与验证的生成文件，不是用例。

计时用例的 Lean 文件都自带 `import Mathlib`（或 `import Mathlib` + `import Lean` 的计时文件），可以单独用
`lake env lean <file>` 检查。计时脚本见 `../harness/bench.py`。

`lean-proof-pipeline/` 只需 `import Lean`，可直接用 Lean 4.31.0 运行；它的输出用于解释证明检查流程，不纳入计时统计。

`quantitative-iteration/` 的历史完整进程记录另见主 README，原始输入的哈希与这里的六份副本一致；不要与不含启动/导入的检查路径样本合并统计。
