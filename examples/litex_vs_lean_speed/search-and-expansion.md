# 求和展开与算术上下文负载

这组例子检验两种检查成本：把一个求和对象逐项展开的成本，以及让算术搜索读取更多无关假设的成本。两侧证明同一个命题；Lean 同时保留展开/全上下文路线和直接路线。全部构造用例都保留，速度方向不决定收录。

Lean 的直接证明在这批中也很短，因此它检验检查成本与表达形状，没有展示大段 Lean 代码的行数压缩。

本批只测各自的原生检查路径，不包含 Litex 编译为 Lean 后的最终核验。测量沿用本目录的 `bench.py`，排除进程启动、Mathlib 导入和输出渲染；不与完整进程批次混合。

## 给数列每项加 c

对任意有理数列 u 和有理数 c，证明给前 N 项的每项加 c 后，总和增加 N*c。取 N=16、64、128，数学证明不随项数增长。

Litex 的主计算保持为求和对象：

```litex
sum(1,16,fn(k N) Q {u(k)+c})=sum(1,16,fn(k N) Q {u(k)})+sum(1,16,fn(k N) Q {c})=sum(1,16,u)+sum(1,16,fn(k N) Q {c})=sum(1,16,u)+16*c
```

完整文件还包括函数类型和全称声明。删减检查确认原来的独立求和线性性、常数和以及结论回显都可由这条链替代；公开源码只保留通过独立检查的短版本。[16 项](sources/search-expansion/affine_sum_16.lit)、[64 项](sources/search-expansion/affine_sum_64.lit)、[128 项](sources/search-expansion/affine_sum_128.lit) 使用同一证明形状。

Lean 的展开路线为：

```lean
intro u c
simp only [Finset.sum_range_succ, Finset.sum_range_zero]
ring
```

直接路线为：

```lean
intro u c
simp [Finset.sum_add_distrib]
```

展开路线用于观察逐项化简的增长；直接路线是必须比较的 Lean 基线。不能把展开路线的成本解释为 Lean 无法使用求和公式。Litex 的闭区间 1..N 对应 Lean 中 `k ∈ Finset.range N` 的 `u(k+1)`，两侧项数、下标和数域相同。

这个实验受 [ProofOptimizer 附录 H.2](https://arxiv.org/pdf/2510.15700) 的慢求和案例启发，但本批是独立构造的命题，不是论文整题的性能复现，也没有搬用论文秒数。

## 同一个平方差结论，增加无关假设

证明 `2*x*y <= x^2+y^2`，分别增加 0、12、24 条 `zi>=0` 假设。它们不参与数学证明，是明确的人造上下文负载；两侧的额外变量和假设完全一致。

Litex 使用平方差恒等式和非负性：

```litex
x^2+y^2-2*x*y=(x-y)^2 >= 0
```

Lean 比较三个路线：

```lean
nlinarith [sq_nonneg (x-y)]
nlinarith only [sq_nonneg (x-y)]
exact two_mul_le_add_sq x y
```

前者读取全部假设，中者限定平方差证书，后者直接引用库中的同形不等式。Litex 的删减控制中，仅保留最终不等式目标未通过，而上面的一行计算通过；无需另写平方非负性或重复最终目标。[0 条](sources/search-expansion/quadratic_context_0.lit)、[12 条](sources/search-expansion/quadratic_context_12.lit)、[24 条](sources/search-expansion/quadratic_context_24.lit) 都是完整、独立可验证的命题。它们不代表更难的数学，也不能外推所有 `nlinarith` 的复杂度。

## 检查与重跑

```bash
cargo build --release
python3 examples/litex_vs_lean_speed/harness/search_expansion.py all --lean-project /path/to/lean-mathlib-project
```

Lean 项目需要已有依赖缓存，工具从其 `lean-toolchain` 选择工具链。省略 `--lean-project` 时使用本仓库既有的 `showcases/litex_to_lean_adapter` 项目。`validate` 只验证，`measure` 重新采样，`all` 顺序运行两者。

- [用例与所有证明路线](cases/search-expansion.json) 和 `sources/search-expansion/` 必须逐字同步，工具会检测漂移。
- 每份 Litex 文件通过独立的 `-strict -f` 检查；Lean 验证包打印全部定理的公理依赖并拒绝 `sorryAx`。
- 每题有一个邻近错误结论：求和系数从 N 改成 N+1，或把不等式中的 2 改成 3。它们必须在证明搜索阶段被拒绝，解析失败不算通过负例控制。
- 计时器还接收一次 `0=1` 的失败 Lean 证明，确认输出字符串 `false` 不会被当成成功样本。
- 每侧 3 个进程；Litex 每题每进程 10 次、Lean 每路线每进程 3 次暖样本。两侧均额外记录每进程的首次调用，不混入暖样本中位数，共保留 198 条 Litex 样本和 180 条 Lean 样本。两个系统的运行时初始化、语法解析与采样数边界沿用主 README 的说明。
- 生成的验证/重复包、Rust 计时器和负例文件留在任务草稿区；公开目录保存源题、源码、原始样本、摘要与环境/源码哈希。可执行文件和 Rust 库在运行前复制为固定快照，复制前后校验哈希，计时器仅链接该快照；其他并行 Cargo 构建不会替换本轮使用的文件。

[结果表](results/search-expansion.md) · [逐样本数据](results/search-expansion-raw.json) · [摘要](results/search-expansion-summary.json) · [验证与拒绝控制](results/search-expansion-validation.json) · [环境与源码哈希](results/search-expansion-environment.json)

## 本轮结果：2026-10-24

本机 Darwin arm64、Lean 4.31.0、Litex 1.1.2-beta 的暖样本中位数如下，单位为毫秒；数值越小越快。全部 378 条样本保留，包括首次调用和较慢的样本。完整结果表还列出 `nlinarith only`，摘要包含各路线的最小、最大值。

| 命题 | Litex | Lean 展开/全上下文 | Lean 直接公式/引理 |
| --- | ---: | ---: | ---: |
| 求和 16 项 | 44.100 | 45.868 | 12.584 |
| 求和 64 项 | 42.909 | 238.339 | 12.637 |
| 求和 128 项 | 42.918 | 762.758 | 13.307 |
| 二次不等式，0 条无关假设 | 10.911 | 79.257 | 25.834 |
| 二次不等式，12 条无关假设 | 56.551 | 229.048 | 31.422 |
| 二次不等式，24 条无关假设 | 120.350 | 707.885 | 40.023 |

求和对象保持为公式时，Litex 的检查时间在三种 N 上约为 43–44 ms；Lean 逐项展开从约 46 ms 增长到 763 ms。Lean 改用求和线性性后，三题都约为 13 ms。128 项时，改进 Lean 路线本身就让检查快了约 57 倍，因此该题不能作为 Litex 优于直接 Lean 证明的证据。

算术上下文负载也影响 Litex：从 0 到 24 条无关假设，约从 11 ms 增长至 120 ms。Lean 的 `nlinarith only` 在 24 条时约 109 ms，直接引用引理约 40 ms；精简搜索范围是有效的 Lean 对照。0 条时 Litex 约 11 ms，快于本次测得的 Lean 直接引理路线约 26 ms。六个例子中，Lean 的直接路线在五个例子上更快。

这批支持继续研究“保留数学对象”和“显式给证书”的检查成本，也显示需要测量 Litex 自身的上下文开销。当前例子没有展示大量 Lean 代码被压短，也没有测量放回 Lean 大证明后的总成本。工作区有未提交修改，环境中的 Git commit 只作基线标识；被测构建以固定二进制和 rlib 哈希识别。原始数据可见单次波动，本表是当前机器与具体路线的描述。

完整 AIME1984 P1 的尝试没有计入这六个正例：当前作者代码仍未完成“由通项相等推出求和相等”这一步。它与本批已经独立验证的平移和恒等式不同；不能把这些小接口的成功称作完成原题。
