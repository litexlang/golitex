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

命名约定：

- `<case>.lit`：Litex 源码，一例一个文件。
- `<case>_<method>.lean` 或 `<case>__<method>.lean`：同一命题的一条 Lean 证明路线；
  批次之间的分隔符不同（`_` 与 `__`），保持与各自批次记录一致。
- `new-round/Repeat.lean`、`new-round/Validate.lean`：本目录计时与验证的生成文件，不是用例。

Lean 文件都自带 `import Mathlib`（或 `import Mathlib` + `import Lean` 的计时文件），可以单独用
`lake env lean <file>` 检查。计时脚本见 `../harness/bench.py`。
