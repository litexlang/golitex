# Litex / Lean 检查耗时对照

本目录把到目前为止做过的 Litex / Lean 计时实验集中到一处：每一条用例在两侧写同一个数学命题，分别测量各自的检查路径，并保留可复现的源码、原始样本和环境快照。

新增的[求和展开与算术上下文负载](search-and-expansion.md)批次包含 6 份完整 Litex 例子和 15 条 Lean 路线，比较展开/全上下文与直接 Lean 基线。本批保留全部结果，不采用下文既有批次“只收 Litex 更快”的筛选口径；检查路径耗时与完整进程耗时仍分开记录。

<!-- quantitative-iteration-table:start -->
## 定量迭代：完整进程耗时（秒）

| 问题 | 速度：Litex 耗时中位数（秒）↓ | 速度：Lean 耗时中位数（秒）↓ | 速度：Litex 加速比（Lean 耗时÷Litex 耗时）↑ |
| --- | ---: | ---: | ---: |
| [参数化 Newton 单步](#iteration-parametric-newton) | 0.213 | 60.180 | 283.09× |
| [二次函数梯度下降](#iteration-quadratic-descent) | 2.905 | 21.303 | 7.33× |
| [含扰动的几何递推界](#iteration-perturbed-geometric) | 1.352 | 17.130 | 12.67× |

测量日期 2026-10-24，每侧每题 3 个样本，比值用未舍入中位数计算。这是启动新进程到完整文件检查结束的耗时，**包括 Lean 的 Mathlib 导入**。它与下方既有批次的不含启动/导入的毫秒表分开记录；比值不表示纯验证器或证明搜索加速比。

[原始样本](results/quantitative-iteration-raw.json) · [汇总](results/quantitative-iteration-summary.json) · [环境与源码哈希](results/quantitative-iteration-environment.json) · [验证记录](results/quantitative-iteration-validation.json)。本批使用记录的 release 二进制；没有把源码搬到此路径后重新计时。
<!-- quantitative-iteration-table:end -->

从真实证明项理解比较机制，见 [为什么Litex计算1+1=2比Lean快了30倍？截然不同的运行架构和对数学证明的理解的选择。](lean-proof-pipeline.md)：逐步展示源码、显式核心项、lambda 与内核的定义相等检查。这是解释实验，没有新增耗时数据，也不从 lambda calculus 本身推断性能。

聚焦类型与对象表达的四组对照，见 [Types, objects, and ordinary mathematical notation](types-and-objects.md)：跨数集推理、整数商余分解、带条件函数调用和有限集合计数，并列出各组源码长度与已有检查耗时。

类型桥接是否解释速度差异，见 [What numeric type bridges cost in these examples](type-bridge-experiment.md)：同一 Lean 命题的转换标注、转换自动化与直接引理对照，并分项测量目标展开、证明构造和最终声明检查。本实验保留全部对照结果，不按哪一侧更快筛选。

```text
cases/            本轮用例定义（JSON：Litex 源码、Lean 命题、每条 Lean 证明路线）
sources/          每例的 Litex 与 Lean 源码，按批次与领域分目录
harness/bench.py  重跑计时（validate / measure / all）
results/          原始样本、汇总、验证记录、环境快照
```

## 怎么读这些数字

- 既有检查路径表的单位为毫秒，数值为暖样本中位数；**倍率 = Lean ÷ Litex**，大于 1 表示 Litex 更快。
- 这些检查路径批次的两侧都**不含**进程启动和 `import Mathlib`。完整的命令行耗时另有一套数量级更大的数字，不在这里混算。
- Litex：release 构建，每个样本新建严格 `Runtime`；计时覆盖词法、解析、良定义性检查、验证、存储与证据构建。
- Lean：`#probe` 自定义命令用纳秒时钟包裹 `elabCommand`，`Elab.async=false` 让证明构造与内核检查同步；计时不含命令解析。
- 这些是两条**检查路径**的对照，不是语言或内核的总体排名，也不是作者完成数学任务所需时间的同比缩短。

<a id="de-bruijn-factor"></a>

### 德布鲁因因子：形式化比普通数学多写多少

**德布鲁因因子（de Bruijn factor）= 形式化文本长度 ÷ 非形式化数学文本长度**。因子越小，额外书写越少：1.5 表示长 50%，0.8 表示短 20%。它与检查速度分别列出，展示同一个用例的表达长度和运行耗时。[Wiedijk 原文](https://www.cs.ru.nl/~freek/factor/factor.pdf)讨论了这个比值，以及未压缩和压缩文件的不同计量方式。

本页新增的 **DF\*** 沿用既有源码对比的有效字符口径：去掉空白、整行注释、导入、`set_option` 和 `#` 开头的验证指令，计 Unicode 字符；计入声明、名字、命题和证明，不展开两侧已载入的库或内置规则。非形式化文本只去掉空白。两侧共用同一份英文数学文本，包含对应的命题、条件和证明或计算说明。DF\* 是字符计量的变体，不是文献中的原始字节或 gzip 因子。

例如商余分解的共同文本是：

> For an integer a and a positive integer d, a = d⌊a/d⌋ + (a mod d), by quotient-remainder decomposition.

**表格左侧的“表达”两列比较德布鲁因因子，右侧的“速度”三列比较运行耗时。**计算方向分别是：

- **表达长度：**Litex 德布鲁因因子 = Litex 字符数 ÷ 普通数学字符数；Lean 德布鲁因因子 = Lean 字符数 ÷ 同一份普通数学字符数。两个因子都越小越简短。
- **运行速度：**两个耗时都以毫秒计，越小越快；Litex 加速比 = Lean 耗时 ÷ Litex 耗时，越大表示 Litex 越快。

| 用例 | 表达：Litex 德布鲁因因子 DF* ↓ | 表达：Lean 德布鲁因因子 DF* ↓ | 速度：Litex 耗时 (ms) ↓ | 速度：Lean 耗时 (ms) ↓ | 速度：Litex 加速比（Lean 耗时÷Litex 耗时）↑ |
| --- | ---: | ---: | ---: | ---: | ---: |
| 整数商余分解 | 0.35 | 1.24 | 1.135 | 3.341 | 2.94× |
| √2 无理数完整证明 | 1.73 | 4.91 | 199.285 | 779.754 | 3.91× |

例如第一行的两个因子是 **30÷85 = 0.35、105÷85 = 1.24**，加速比是 **3.341375÷1.135042 = 2.94×**；计算使用未舍入数据。这里的 Lean 路线沿用各表的既有计时选择，不另挑较长源码放大差距，也不代表最短可能写法。

**这些是回溯示例**：[共同非形式化文本](cases/informal-baselines.json)是在已有形式化源码之后补写的，不是预先选定原文的翻译实验。因此不汇总成“Litex 的固定德布鲁因因子”，也不能据此直接推出更易读或更易写。分母的语言、记号和详细程度会影响数值；后续正式实验应先固定原文再独立形式化。现有结果也保留 Lean 更短的行，例如幂集基数、奇数谓词和互反序列。

本次覆盖三个生成批次的 24 例及类型指南中的带条件倒数。两条多步用例的当前 `.lit` 已比计时用例定义增加了证明步骤，因子标为 **—**；其余旧批次尚未补齐共同原文。[逐例字符数、源码哈希与两条差异记录](results/de-bruijn-factors.json)可由 `python3 examples/litex_vs_lean_speed/harness/de_bruijn.py --check` 复核；`--write` 只从保存的数据重建长度记录和三张结果表，不重新测速。

## 总览

下表只统计既有检查路径批次；完整进程的三组实验单独列在本页开头。

| 领域 | 例数 | 运行速度：加速比范围（Lean 耗时÷Litex 耗时） |
| --- | ---: | ---: |
| 自然数算术与根式 | 2 | 14× – 37× |
| 有限求和 | 4 | 3.5× – 7.3× |
| 三角 | 3 | 10× – 19× |
| 初等计算：对数、根式、大数 | 5 | 7× – 217× |
| 数论：素性与最大公因数 | 2 | 2.2× – 147× |
| 量词、见证、唯一存在、存在消去 | 21 | 1.1× – 77× |
| 定义与证明命令（函数、谓词、结构、反证、分类、归纳） | 9 | 4.0× – 51× |
| 集合 | 3 | 1.6× – 82× |
| 函数（值域） | 1 | 2.9× |
| 整数算术与整除 | 2 | 2.8× – 2.9× |
| 有限组合 | 2 | 4.2× – 73× |
| 微积分（连续、导数） | 2 | 24× – 30× |
| 经典大证明（√2 无理，两侧同步骤） | 1 | 3.9× |
| 多步命题（第二轮：不等式/代数/算术/存在构造） | 7 | 1.7× – 306× |
| 其它语句形式与 showcase 小问题（第三轮：谓词定义/见证/ε-N/集合相等） | 4 | 3.7× – 8.8× |

**既有检查路径批次的收录口径：**只收 Litex 检查更快（倍率 > 1）的用例，倍率按两侧同一命题、同一工作量计算。Lean 更快的方向（函数外延相等靠定义归约、递归显式展开、直接引用一条已证完的大定理）不在本目录内。

---

## 一、已有的五批实验

这五批的原始样本保存在本仓库的本地批次记录里（五个 `2026-10-22-*` / `2026-10-23-*` 目录）。这里发布的是每例的源码与汇总数字；这些数字是读取当时的记录，没有重新测量，环境见 `results/`。

### 1. 基础算术与根式（2026-10-22）

| 数学语句 | 速度：Litex 耗时 (ms) ↓ | 速度：Lean 最快耗时 (ms) ↓ | 速度：Litex 加速比（Lean 耗时÷Litex 耗时）↑ | Lean 路线 | 源码 |
| --- | ---: | ---: | ---: | --- | --- |
| `1 + 1 = 2`（Mathlib 已载入） | 0.037 | 1.361 | **36.66×** | `rfl` | [lit](sources/arithmetic/add.lit) · [lean](sources/arithmetic/mathlib_nat.lean) |
| `sqrt(1) = 1` | 0.039 | 0.555 | **14.28×** | `Real.sqrt_one` | [lit](sources/arithmetic/sqrt.lit) · [lean](sources/arithmetic/sqrt_exact.lean) |

### 2. 有限求和与三角（2026-10-22）

| 数学语句 | 速度：Litex 耗时 (ms) ↓ | 速度：Lean 最快耗时 (ms) ↓ | 速度：Litex 加速比（Lean 耗时÷Litex 耗时）↑ | Lean 路线 | 源码 |
| --- | ---: | ---: | ---: | --- | --- |
| `sum(1,10,fn(k Z) Z {k}) = 55` | 1.623 | 5.622 | **3.46×** | `decide` | [lit](sources/sums/sum_id_10.lit) |
| `sum(1,10,fn(k Z) Z {k^2}) = 385` | 2.224 | 8.266 | **3.72×** | `decide` | [lit](sources/sums/sum_sq_10.lit) |
| `sum(1,10,fn(k Z) Q {1/3}) = 10/3` | 2.123 | 11.277 | **5.31×** | `sum_const` + `norm_num` | [lit](sources/sums/sum_rat_10.lit) |
| `finite_set_sum({1,3,5,7,9}, fn(k Z) Z {k}) = 25` | 1.108 | 8.051 | **7.26×** | `decide` | [lit](sources/sums/finite_set_5.lit) |
| `sin(0) = 0` | 0.041 | 0.757 | **18.43×** | `Real.sin_zero` | [lit](sources/sums/sin_zero.lit) · [lean](sources/sums/sin_zero__exact.lean) |
| `sin(pi) = 0` | 0.040 | 0.736 | **18.50×** | `Real.sin_pi` | [lit](sources/sums/sin_pi.lit) · [lean](sources/sums/sin_pi__exact.lean) |
| `forall x R: sin(x)^2 + cos(x)^2 = 1` | 0.446 | 4.636 | **10.40×** | `fun x => Real.sin_sq_add_cos_sq x` | [lit](sources/sums/sin_identity.lit) · [lean](sources/sums/sin_identity__exact.lean) |

有限求和是这批里倍率最低的一类：两边都在逐项求和，Litex 的优势来自没有证明项构造。

### 3. 初等计算、数论与大数（2026-10-22）

| 数学语句 | 速度：Litex 耗时 (ms) ↓ | 速度：Lean 最快耗时 (ms) ↓ | 速度：Litex 加速比（Lean 耗时÷Litex 耗时）↑ | Lean 路线 | 源码 |
| --- | ---: | ---: | ---: | --- | --- |
| `log(2,8) = 3` | 0.064 | 13.992 | **217.01×** | 显式重写（`logb_pow` 等） | [lit](sources/elementary/log_2_8.lit) · [lean](sources/elementary/log_2_8_explicit.lean) |
| `sqrt(2)*sqrt(8) = 4` | 0.240 | 7.077 | **29.50×** | `sqrt_mul` + `norm_num` | [lit](sources/elementary/radical_product.lit) |
| `$prime(1000000007)` | 0.027 | 4.029 | **147.19×** | `native_decide` | [lit](sources/elementary/prime_1000000007.lit) · [lean](sources/elementary/prime_1000000007_native_decide.lean) |
| `factorial(50) = 30…000`（精确值） | 0.107 | 2.501 | **23.41×** | `norm_num` | [lit](sources/elementary/factorial_50.lit) · [lean](sources/elementary/factorial_50_norm_num.lean) |
| `95800^4+217519^4+414560^4 = 422481^4` | 0.264 | 11.098 | **42.03×** | `rfl` | [lit](sources/elementary/fourth_power_eq.lit) · [lean](sources/elementary/fourth_power_eq_rfl.lean) |
| `witness exist a,b,c,d N+ st {a^4+b^4+c^4=d^4} from …` | 2.094 | 14.718 | **7.03×** | `decide` | [lit](sources/elementary/fourth_power_witness.lit) |
| `gcd(2178309,1346269) = 1` | 0.455 | 0.992 | **2.18×** | `rfl` | [lit](sources/elementary/gcd_2178309.lit) |

素性一例的 Lean 路线用的是 `native_decide`：它在本机编译求值，`#print axioms` 会记录一条生成公理依赖。同一目标用 `norm_num` 需要 718 ms。表里取的是**已测最快**写法，所以这是对 Lean 有利的比较。

### 4. 量词、见证、唯一存在与存在消去（2026-10-23，21 例）

每例都测了 tactic、直接引理与简短证明项多条路线，下表取每题已测最快的 Lean 写法。“语句形状”指这条命题主要考的是哪种 Litex 语句。

| 语句形状 | 数学语句 | 速度：Litex 耗时 (ms) ↓ | 速度：Lean 耗时 (ms) ↓ | 速度：Litex 加速比（Lean 耗时÷Litex 耗时）↑ |
| --- | --- | ---: | ---: | ---: |
| 全称 + 加法保号 | 两正实数之和为正 | 0.394 | 9.305 | **23.60×** |
| 全称 + 乘法保号 | 两正实数之积为正 | 0.408 | 4.986 | **12.23×** |
| 全称 + 传递 | 严格不等式的传递性 | 0.256 | 1.240 | **4.84×** |
| 全称 + 不等式平移 | 不等式两边加上同一实数 | 0.469 | 9.537 | **20.33×** |
| 全称 + 幂 | 任意实数的平方非负 | 0.597 | 13.491 | **22.60×** |
| 全称 + 绝对值 | 绝对值三角不等式 | 5.261 | 7.338 | **1.39×** |
| 全称 + 倒数 | 正实数的倒数为正 | 0.287 | 8.167 | **28.43×** |
| 全称 + 除法 | 非零实数除以自身等于一 | 0.387 | 3.301 | **8.52×** |
| 全称 + 反对称 | 双向弱不等式推出相等 | 0.287 | 1.217 | **4.24×** |
| 全称 + 析取结论 | 零乘积推出一个因子为零 | 0.203 | 6.860 | **33.83×** |
| 全称 + 多项式恒等式 | 平方展开式 | 1.589 | 15.006 | **9.44×** |
| 全称 + 实例化 | 把全称函数性质用到 0 上 | 0.675 | 1.238 | **1.83×** |
| 见证 | 实数平方等于四 | 0.512 | 4.789 | **9.36×** |
| ∀∃ 构造 | 对每个实数构造更大的实数 | 1.071 | 1.384 | **1.29×** |
| ∀∃ + 正性 | 给定正数构造更小的正数 | 1.628 | 10.215 | **6.28×** |
| 唯一存在 | 每个实数有唯一加法逆元 | 1.422 | 3.795 | **2.67×** |
| ∀∃ 双约束 | 构造和与差都给定的两个实数 | 3.219 | 21.098 | **6.56×** |
| 存在消去 | 由平方根存在推出非负 | 4.148 | 14.026 | **3.38×** |
| 存在消去 + 换尺度 | 提取平方根后构造四倍数平方根 | 9.502 | 14.557 | **1.53×** |
| ∀∃ + 上界 | 为两个实数构造共同上界 | 1.745 | 1.871 | **1.07×** |
| 非空集合见证 | 用见证证明正实数集合非空 | 0.084 | 6.439 | **76.88×** |

源码在 `sources/quantifiers/`：每例一个 `.lit`，每条 Lean 路线一个 `<id>_<method>.lean`。

这 21 例说明一个规律：**命题里需要的良定义性、作用域和规则越多，Litex 的优势越大**；当 Lean 有专门的一行引理（`lt_trans`、`le_antisymm`、`exists_gt`、`abs_add_le`）时，差距塌到 1–5 倍。

### 5. 定义与证明命令（2026-10-23，10 个程序）

整段程序（定义 + 使用，或完整证明块）的耗时：

| 程序 | 速度：Litex 耗时 (ms) ↓ | 速度：Lean 耗时 (ms) ↓ | 速度：Litex 加速比（Lean 耗时÷Litex 耗时）↑ | 源码 |
| --- | ---: | ---: | ---: | --- |
| 表达式函数：定义平方并计算 | 0.730 | 7.609 | **10.42×** | [lit](sources/declarations/expression_function.lit) · [lean](sources/declarations/expression_function.lean) |
| 带定义域条件的倒数函数 | 1.823 | 8.583 | **4.71×** | [lit](sources/declarations/guarded_function.lit) · [lean](sources/declarations/guarded_function.lean) |
| 开区间谓词定义与使用 | 0.189 | 8.223 | **43.45×** | [lit](sources/declarations/predicate.lit) · [lean](sources/declarations/predicate.lean) |
| 按正负分段定义绝对值 | 0.729 | 7.330 | **10.05×** | [lit](sources/declarations/piecewise_function.lit) · [lean](sources/declarations/piecewise_function.lean) |
| 二维点结构、构造与字段访问 | 0.573 | 7.615 | **13.30×** | [lit](sources/declarations/structure.lit) · [lean](sources/declarations/structure.lean) |
| 定义并调用“正实数非零”定理 | 0.158 | 8.018 | **50.74×** | [lit](sources/declarations/named_theorem.lit) · [lean](sources/declarations/named_theorem.lean) |
| 反证：不存在平方等于 -1 的实数 | 4.127 | 49.472 | **11.99×** | [lit](sources/declarations/contradiction.lit) · [lean](sources/declarations/contradiction.lean) |
| 分类讨论：绝对值等于原数或其相反数 | 0.757 | 10.576 | **13.97×** | [lit](sources/declarations/cases_proof.lit) · [lean](sources/declarations/cases_proof.lean) |
| 归纳证明前 n 个正整数的求和公式 | 43.626 | 174.986 | **4.01×** | [lit](sources/declarations/induction_proof.lit) · [lean](sources/declarations/induction_proof.lean) |

这批还分别测了“只声明定义”和“在已载入定义的新上下文中使用定义”两段，见 `results/selected-cases-2026-10-22-23.csv` 之外的原始记录。

---

## 二、本轮新增：更宽的领域（2026-10-23）

这一轮补的是前五批没覆盖的领域：集合、函数、整数算术与整除、有限组合、微积分，以及一个“稍微大一点”的经典证明。用例定义在 `cases/new-round.json`，源码在 `sources/new-round/`，原始样本在 `results/new-round-raw.json`。

| 领域 | 数学语句 | Litex 写法要点 | Lean 写法要点 | 表达：Litex 德布鲁因因子 DF* ↓ | 表达：Lean 德布鲁因因子 DF* ↓ | 速度：Litex 耗时 (ms) ↓ | 速度：Lean 耗时 (ms) ↓ | 速度：Litex 加速比（Lean 耗时÷Litex 耗时）↑ |
| --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: |
| 经典大证明 | √2 不是有理数 | `by contra:` + 唯一既约分数 + 素数整除幂，推出 p、q 同为偶数 | 同五步：`Rat.num`/`Rat.den` 互素 + 奇偶性 + `Nat.Prime.dvd_of_dvd_pow` | 1.73 | 4.91 | 199.285 | 779.754 | **3.91×** |
| 集合 | 并交分配律 | `union(A,intersect(B,D))=intersect(union(A,B),union(A,D))` | `Set.union_inter_distrib_left` | 1.08 | 1.09 | 0.286 | 1.380 | **4.83×** |
| 集合 | 差集对并集的德摩根律 | `set_minus(A,union(B,D))=intersect(set_minus(A,B),set_minus(A,D))` | `ext` + `simp` + `tauto` | 0.85 | 1.16 | 0.279 | 22.842 | **81.96×** |
| 集合 | 交集保持包含 | `A $subset B =>: intersect(A,D) $subset intersect(B,D)` | `Set.inter_subset_inter_left` | 0.99 | 1.00 | 0.934 | 1.500 | **1.61×** |
| 函数 | 函数值属于值域 | `f(x) $in fn_range(f)` | `Set.mem_range_self` | 0.68 | 1.36 | 0.313 | 0.920 | **2.94×** |
| 整数算术 | 整数除法的商余分解 | `a=d*quot(a,d)+a%d` | `Int.mul_ediv_add_emod` | 0.35 | 1.24 | 1.135 | 3.341 | **2.94×** |
| 整除 | 整数乘积被其因子整除 | `$dvd(a*c,c)` | `dvd_mul_left` | 0.52 | 1.24 | 0.604 | 1.712 | **2.83×** |
| 有限组合 | `{1,2,3}` 的元素个数 | `finite_set_size({1,2,3})=3` | `by decide` | 0.44 | 0.75 | 0.049 | 3.597 | **73.43×** |
| 有限组合 | n 元集合有 2ⁿ 个子集 | `finite_set_size(power_set(A))=2^finite_set_size(A)` | `Finset.card_powerset` | 0.84 | 0.78 | 0.250 | 1.047 | **4.19×** |
| 组合 | 自然数阶乘为正 | `factorial(n)>0` | `Nat.factorial_pos` | 0.42 | 0.98 | 0.165 | 0.582 | **3.54×** |
| 微积分 | x² 在 3 处的导数为 6 | `$has_derivative_at(fn(t R) R {t^2},3,6)` | `hasDerivAt_pow` + `congr_deriv` + `norm_num` | 0.80 | 3.07 | 1.555 | 46.258 | **29.75×** |
| 笛卡尔积 | 有序对的坐标重构 | `(p(1),p(2))=p` | `Prod.mk.eta` | 0.35 | 0.67 | 0.170 | 0.567 | **3.34×** |
| 微积分 | x² 在 3 处连续 | `$is_continuous_at(fn(t R) R {t^2},3)` | `continuousAt_pow` | 0.59 | 1.14 | 0.377 | 8.986 | **23.83×** |

同一个命题在 Lean 侧换写法，差别可能很大，所以每条备选路线都单独测了：

| 用例 | Lean 路线 | 写法提要 | 速度：Lean 耗时 (ms) ↓ | 速度：Litex 加速比（Lean 耗时÷Litex 耗时）↑ |
| --- | --- | --- | ---: | ---: |
| 并交分配律 | `lemma`（主表口径） | 引用与目标同形的 Mathlib 引理 | 1.380 | 4.83× |
| 并交分配律 | `ext_simp` | `ext x` + `simp` + `tauto` 自己拆集合 | 34.521 | 120.85× |
| 交集保持包含 | `lemma`（主表口径） | 引用与目标同形的 Mathlib 引理 | 1.500 | 1.61× |
| 交集保持包含 | `term` | 直接给出证明项 | 2.053 | 2.20× |
| 集合 {1,2,3} 的元素个数 | `decide`（主表口径） | `by decide` | 3.597 | 73.43× |
| 集合 {1,2,3} 的元素个数 | `norm_num` | `by norm_num` | 19.045 | 388.83× |
| 有序对的坐标重构 | `term` | 直接给出证明项 | 0.632 | 3.72× |
| 有序对的坐标重构 | `lemma`（主表口径） | 引用与目标同形的 Mathlib 引理 | 0.567 | 3.34× |

主表每行标注的路线写在该表的“Lean 最快路线”列里，`results/new-round.md` 也有同样一列。倍率一律用未舍入的中位数计算。

每行都另有完整源码（每条 Lean 路线一个文件）：`sources/new-round/<id>.lit`、`sources/new-round/<id>__<method>.lean`。

### √2 无理数：两侧按同一套步骤做完

两边都做同样五步：反证设 √2 是有理数 → 取唯一既约分数 p/q（gcd(p,q)=1）→ 由 p² = 2q² 得 2 | p²，从而 p 是偶数 → 代回得 q² = 2(p/2)²，从而 q 也是偶数 → 与 gcd(p,q)=1 矛盾。Litex 用 `release thm` 取两条辅助定理（唯一既约分数、素数整除幂），Lean 侧对应 `Rat.reduced` 与 `Nat.Prime.dvd_of_dvd_pow`。

Litex（199.285 ms）：

```litex
# sqrt(2) is not rational.
by contra:
    ? not sqrt(2) $in Q
    release thm rational_has_unique_reduced_fraction(sqrt(2))
    obtain p, q from exist! p Z, q N+ st {sqrt(2) = p / q, gcd(p, q) = 1}

    p^2 = (sqrt(2) * q)^2 = sqrt(2)^2 * q^2 = 2 * q^2
    p^2 % 2 = (2 * q^2) % 2 = 0
    release thm prime_divides_power(p, 2, 2)

    p / 2 $in Z
    q^2 = p^2 / 2 = 2 * (p / 2)^2
    q^2 % 2 = (2 * (p / 2)^2) % 2 = 0
    release thm prime_divides_power(q, 2, 2)

    impossible 2 <= gcd(p, q) = 1
```

Lean（779.754 ms，[源码](sources/new-round/sqrt_two_irrational__scratch.lean)）：

```lean
import Mathlib

example : Irrational (Real.sqrt 2) := by
  rintro ⟨q, hq⟩
  have h2 : (q : Real) ^ 2 = 2 := by
    rw [hq, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  -- 唯一既约分数：p = |num|, m = den, gcd p m = 1
  set p : Nat := q.num.natAbs with hp
  set m : Nat := q.den with hm
  have hden : (m : Real) ≠ 0 := by
    have : (0 : Nat) < m := q.den_pos
    exact_mod_cast this.ne'
  -- 把 (q : ℝ) = num / den 代入
  have hqeq : (q : Real) = (q.num : Real) / (m : Real) := by
    rw [Rat.cast_def, hm]
  -- p² = 2 m²（先把 ℤ 上的等式转成 ℕ）
  have hnat : p ^ 2 = 2 * m ^ 2 := by
    have hreal : (q.num : Real) ^ 2 = 2 * (m : Real) ^ 2 := by
      rw [hqeq] at h2
      field_simp at h2
      nlinarith [h2]
    have hint : q.num ^ 2 = 2 * (m : Int) ^ 2 := by
      exact_mod_cast hreal
    have habs : ((p : Int)) ^ 2 = 2 * (m : Int) ^ 2 := by
      have hnum : q.num ^ 2 = ((p : Int)) ^ 2 := by
        rcases Int.natAbs_eq q.num with h | h
        · rw [h, hp]
        · rw [h, hp]; ring
      rw [← hnum, hint]
    exact_mod_cast habs
  -- p 是偶数
  have hp2 : 2 ∣ p ^ 2 := ⟨m ^ 2, hnat⟩
  have hp_even : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hp2
  -- 于是 q 也是偶数
  obtain ⟨k, hk⟩ := hp_even
  have hm2 : m ^ 2 = 2 * k ^ 2 := by
    rw [hk] at hnat
    nlinarith
  have hm2dvd : 2 ∣ m ^ 2 := ⟨k ^ 2, hm2⟩
  have hm_even : 2 ∣ m := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hm2dvd
  -- 与 gcd(p, m) = 1 矛盾
  have hcop : p.Coprime m := q.reduced
  have hgcd : 2 ∣ p.mgcd m := Nat.dvd_gcd ⟨k, hk⟩ hm_even
  rw [hcop] at hgcd
  omega
```

这是两边同工作量的结果：**Litex 3.91×，绝对时间 199.285 ms，Lean 779.754 ms**。Lean 侧这个证明是本轮从零写的第一版，没有针对速度优化（`field_simp`、`nlinarith`、`exact_mod_cast` 都偏重），熟练的 Lean 用户很可能写得更快；如果后续有优化版本，应当在同一张表里替换。

## 三、多步命题：Lean 没有现成定理可套（2026-10-23 第二轮）

上一轮的教训是：Lean 一侧引用一条与目标同形的定理，不算“更快”。这一轮专门挑 Lean 没有同形定理、必须自己推几步的命题：用例在 `cases/multi-step.json`，源码在 `sources/multi-step/`，每条备选 Lean 路线都单独计时。

| 领域 | 数学语句 | Litex 写法 | Lean 写法 | 表达：Litex 德布鲁因因子 DF* ↓ | 表达：Lean 德布鲁因因子 DF* ↓ | 速度：Litex 耗时 (ms) ↓ | 速度：Lean 耗时 (ms) ↓ | 速度：Litex 加速比（Lean 耗时÷Litex 耗时）↑ |
| --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: |
| 不等式 | 平方和为零则两数都为零 | `x^2+y^2=0 =>: x=0 and y=0` | `constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]` | 0.42 | 1.19 | 0.685 | 209.744 | **306.11×** |
| 不等式 | 正数的 `x/(x+1)` 为正 | 先证 `x+1 > 0`，再证 `x/(x+1) > 0` | `have h1 : 0 < x+1 := by linarith`；`div_pos hx h1` | 0.37 | 1.11 | 0.949 | 29.170 | **30.75×** |
| 代数 | 等式两边同乘 2 的消去 | `2*x = 2*y =>: x = y` | `mul_left_cancel₀ (by norm_num) h` | 0.43 | 1.54 | 0.335 | 10.726 | **32.01×** |
| 不等式 | 实数的平方加一为正 | `x^2 + 1 > 0` | `positivity` | 0.39 | 1.07 | 2.189 | 17.404 | **7.95×** |
| 不等式 | `x² + y² ≥ 2xy` | `(x-y)^2 >= 0` → 展开 → `x^2+y^2 >= 2*x*y` | `nlinarith [sq_nonneg (x-y)]` | 1.02 | 1.34 | 52.271 | 87.954 | **1.68×** |
| 存在构造 | 任意正整数之上都有偶数 | `witness … from 2*n`，再证整除与大于 | `⟨2*n, by omega, by omega, ⟨n, by ring⟩⟩` | — | — | 4.426 | 34.877 | **7.88×** |
| 算术 | 正整数小于它的两倍 | `2*n > n` | `omega` | — | — | 0.885 | 14.761 | **16.69×** |

每条用例的完整源码在 `sources/multi-step/`：`<id>.lit` 与 `<id>__<method>.lean`。

同一命题的其它 Lean 路线（主表用最快的）：

| 用例 | Lean 路线 | 速度：Lean 耗时 (ms) ↓ | 速度：Litex 加速比（Lean 耗时÷Litex 耗时）↑ |
| --- | --- | ---: | ---: |
| 等式两边同乘 2 的消去 | `linarith` | 37.737 | 112.63× |
| 等式两边同乘 2 的消去 | `mul_left_cancel₀`（主表） | 10.726 | 32.01× |
| 实数的平方加一为正 | `positivity`（主表） | 17.404 | 7.95× |
| 实数的平方加一为正 | `nlinarith` | 49.474 | 22.60× |
| 正整数小于它的两倍 | `omega`（主表） | 14.761 | 16.69× |
| 正整数小于它的两倍 | `nlinarith` | 63.217 | 71.47× |

两条值得单独说明：

- **`x² + y² ≥ 2xy` 只有 1.68×。** Litex 要走三步（母不等式、展开成 `x^2 + y^2 - 2*x*y >= 0`、移项），每步都要重新检查一遍；Lean 的 `nlinarith` 一次把三步一起做完。Litex 单条语句便宜，但“语句条数 × 每条成本”不一定便宜。

这一轮还有几条想比但 Litex 侧没能通过自动验证的语句（保留下来当边界记录）：

| 想比的语句 | Litex 的结果 | 处理 |
| --- | --- | --- |
| `∀ a b c, a \| b → a \| (c*(b+a))` | 求和那一步过不去（`$dvd` 不能直接对和式合成） | 换成“两个偶数之积被 4 整除”，用 `obtain` 显式取见证 |
| `∀ x, x^2 = x → x = 0 ∨ x = 1` | 证明搜索失败 | 未采用 |
| `∀ x y, x*y = 1 → x ≠ 0` | 证明搜索失败 | 未采用 |
| `∀ a, ∃ b, a = 2b ∨ a = 2b+1` | 证明搜索失败 | 未采用 |

这些不是 Lean 更快，而是 Litex 现在自动证不出来；要让它们进表，得先补 Litex 的规则或把证明写成更长的显式步骤。写在这里是为了不让“选录”看起来像“全部”。

这几例合起来说明：去掉“引用现成定理”这个因素之后，Litex 的倍率仍在 1.7×–306× 之间，取决于命题需要几条语句、以及 Lean 有没有便宜的一般 tactic 可套。

## 四、其它语句形式与小问题（2026-10-23 第三轮）

前两轮比的都是“事实语句”（`forall … =>: …` 这类）。这一轮换成别的语句形式和 showcases 里的小问题：自定义谓词的定义加见证、从自定义谓词里取见证再推理、ε-N 风格的极限小问题（来自 `showcases/Functions_and_Change/reciprocal.lit`），以及集合相等（Litex 的三种等式义务之一）。用例在 `cases/statement-forms.json`，源码在 `sources/statement-forms/`。

| 语句形式 | 小问题 | Litex 写法 | Lean 写法 | 表达：Litex 德布鲁因因子 DF* ↓ | 表达：Lean 德布鲁因因子 DF* ↓ | 速度：Litex 耗时 (ms) ↓ | 速度：Lean 耗时 (ms) ↓ | 速度：Litex 加速比（Lean 耗时÷Litex 耗时）↑ |
| --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: |
| 谓词定义 + 见证 | 自定义奇数谓词，见证 7 是奇数 | `prop odd(a Z): exist t Z st {a = 2*t+1}`；`witness $odd(7) from 3` | `∃ t : Int, (7:Int) = 2*t + 1`；`⟨3, by norm_num⟩` | 0.70 | 0.63 | 0.521 | 4.575 | **8.77×** |
| 自定义谓词推理 | 奇数乘 3 加 2 还是奇数 | `obtain k from $odd(n)`；`witness $odd(3*n+2) from 3*k+2:` + 等式链 | `rintro n ⟨k, hk⟩`；`⟨3*k + 2, by omega⟩` | 1.14 | 0.70 | 6.810 | 36.353 | **5.34×** |
| 极限风格（ε-N） | 互反序列 `1/n` 可以任意小 | 定义 `a(n)=1/n`，两行具体计算，再 `claim ? forall ε R+: exist n N+ st {a(n) < ε}` | `obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε`；取 `n+1` | 1.29 | 0.95 | 9.553 | 35.269 | **3.69×** |
| 集合相等的义务 | `A ⊆ B` 时 `A ∪ B = B` | `forall A,B power_set(R): A $subset B =>: union(A,B) = B` | `ext x` + 两个方向，或 `Set.union_eq_right.mpr h` | 0.46 | 0.63 | 0.186 | 1.217 | **6.53×** |

三条口径说明：

- **定义算在谁头上不同。** Litex 的 `prop`/`have fn` 必须在会话里出现，所以定义计入 Litex 的时间；Lean 一侧是展开后的命题（谓词那例）或已载入的引理（极限那例）。也就是说这三例里 Litex 还多做了一步定义，仍然更快。
- **集合相等那例有两种 Lean 写法**：自己 `ext` + 分两个方向是 2.321 ms（12.5×），引用 `Set.union_eq_right` 是 1.217 ms（6.53×）。主表用快的那个。
- **这一轮从 showcases 里试了更多题目**：`The-Mechanics-of-Litex-Proof` 的奇偶分情形证明、`2D_Geometry` 的 SAS、`imo_inequalities` 的几道题，都没有达到收录口径（倍率不足 1，或两侧工作量不对等），未纳入本表。

## 五、覆盖清单：Litex 的功能被覆盖到哪一步

按 Litex 手册的语句词典（S01–S52）与对象词典（O01–O62）对照，**已经测过**的有：

| Litex 功能 | 覆盖情况 |
| --- | --- |
| 原子事实、合取、析取、链式等式 | 已测（零因子、精确计算链、多项式恒等式） |
| 全称事实、共享假设、`=>:` 作用域 | 已测（量词批 21 例） |
| 存在、见证、唯一存在、存在消去（S35–S38） | 已测（含非空集合见证） |
| 局部 `claim`、`obtain`、释放定理（S25、S33） | 已测（√2、存在消去、命名定理复用） |
| 反证、分情形、归纳（S39、S40、S42） | 已测（各一例） |
| 表达式函数、带定义域函数、分段、按情况（S01、S11、S21、S22） | 已测（收录 4 例；递归那例不符合收录口径） |
| 具体谓词与 `by def`（S14） | 已测 |
| 结构体与字段访问（S16） | 已测 |
| 命名定理的声明与调用（S18） | 已测 |
| 精确求值与封闭计算（S51） | 已测（算术、对数、阶乘、素性、根式） |
| 集合运算：并、交、差、幂集、包含（O54–O59） | 已测（分配律、德摩根、单调、幂集基数） |
| 函数：值域、复合、向函数本身的全称量化 | 已测 |
| 有限求和、有限集合求和（S44 相关） | 已测（4 种求和） |
| 三角、对数、指数、根式、阶乘、gcd、素性、连续性、导数 | 已测（各 1–3 例） |

**还没有覆盖**、值得下一轮测的：

| 方向 | 为什么值得测 | 预计难点 |
| --- | --- | --- |
| 极限与积分（连续性本轮已覆盖） | 分析是 Litex 原生重点，Mathlib 的分析证明通常很长，是“大例子”的首选 | 原测试使用旧写法 `lim(fn(t R) R {t^2},3)=9`（现写作 `fn_lim(fn(t R) R {t^2},3)=9`）：Litex 在良定义阶段就拒绝，必须先给出“3 是实数聚点”和“连续蕴含极限”两步。所以极限只能按整段程序比较，不能当裸语句比 |
| 强归纳、最小反例（S43） | 与普通归纳（4.01×）对照能看出差别 | Litex 的归纳作用域写法需要先确定固定模式 |
| 函数原像、替换像（S09、S10） | 前像/像是 Litex 的独立语句形状 | Lean 侧要选 `Set.image`/`Set.preimage` 的对应写法 |
| 集合外延性、函数外延性（S45、S46） | 会直接对上“自由函数相等”这一 Lean 的强项 | Litex 需要完整的定义域条件，写法较长 |
| 模板声明族、可复用证明策略（S17、S20） | Litex 独有的复用机制，Lean 里对应 `variable`/`macro`/tactic | 对应关系不唯一，得先定“同一任务”的标准 |
| 正则性注册：自反、对称、传递（S48–S50） | 自定义谓词的规则注册，Lean 里对应 `instance`/`simp` 引理 | 需要构造自定义谓词的最小例子 |
| 信任、公理、选择、佐恩引理（S23、S24、S30–S32） | 能对照 Lean 的 `Classical.choice`/`propext` 公理依赖 | 属于信任边界问题，不只是速度 |
| 多文件项目与 `-r` 加载（module_manager） | 真实数学库是分模块的 | 应比较“整库首次检查 + 增量检查”而不是单条语句 |
| `-lean` 编译到 Lean 后的复核 | 这是 Litex 独有路径：生成 Lean 再由 Lean 复核 | 需要把“Litex 检查 + Lean 检查”合并计时 |
| `-extractpython` / `-extractc` | 数值/算法抽取是 Litex 的另一条出口 | 与 Lean 的 `native_decide`、`#eval` 对照 |
| `-latex` 与 reading 模式 | 面向读者/教材，不是检查速度 | 更适合做输出质量对照，而非计时 |
| 不可验证输入的反馈（负例） | 对 AI/交互式工作流同样重要：拒绝一个错误步骤要多久、说清原因要多久 | 需要定义“诊断质量”的指标，不能只比毫秒 |
| 大型定理库（AM-GM、Cauchy–Schwarz、几何库） | 才是“从零建库”的真实负载 | 两边都要从空的数学上下文写起，工作量以小时计 |

一个原则：**只要 Lean 侧能用一行现成引理，Litex 就不会快**；Litex 的优势区间是“命题本身带着定义域、量词和多个推理动作，而 Lean 需要 tactic 或手工证明项去搭”。上表的覆盖清单也是按这个原则挑的。

---

## 六、复现

在仓库根目录：

```sh
cargo build --release
python3 examples/litex_vs_lean_speed/harness/bench.py validate   # 逐条验证两侧源码
python3 examples/litex_vs_lean_speed/harness/bench.py measure    # 计时（约 2–3 分钟）
```

- `validate` 会把每个 Litex 文件交给 release 二进制跑一遍，并把每一条 Lean 路线编进一个 `#print axioms` 文件，确认没有 `sorryAx`。
- `measure` 复用同样源码：Litex 侧编译一个链接 `liblitex.rlib` 的 Rust 计时器（每进程 30 个暖样本、三个进程），Lean 侧用 `#probe`（每进程 7 个暖样本、三个进程）。
- Lean 环境通过 `showcases/litex_to_lean_adapter` 里的 `lake env` 取得 `LEAN_PATH`；没有该适配器项目时可以用 `LEAN_PATH` 环境变量直接指定。
- 换用例：改 `cases/new-round.json`（或传 `--cases`），`validate` 会自动生成 `sources/<名字>/` 下的逐例源码。

## 七、这些数字不能说明什么

- 不是 Litex 与 Lean 的总体速度排名。用例是选录的，样本量、二进制快照和机器负载都不同；五批数据来自不同批次构建的二进制。
- 不是内核归约速度的对照。Lean 侧含证明构造与同步内核检查，Litex 侧含解析、良定义性、验证与证据构建，两侧边界的定义不同。
- 既有检查路径表不含用户完成数学任务的时间、编辑器增量检查、内存占用、启动与导入成本；本页新增的完整进程表包含启动与导入。
- 每条 Lean 路线都取的是**本轮已测**写法，不构成 Lean 可能达到的下界；反过来，Litex 侧也没有为每个命题手写最优证明，它用的是内置规则与策略的默认搜索。
- 第二轮那 7 条多步命题是按“Lean 没有同形定理”这一条标准挑的，不是系统枚举；换一批命题，倍率分布会变。第一、二轮的部分用例同样是为覆盖领域而选，不代表各领域的平均表现。
- 既有检查路径批次只收录 Litex 更快的用例（倍率 > 1），所以从表里看不到 Litex 落后于 Lean 的方向；那些方向没有测量记录留在本目录里。

<!-- quantitative-iteration-code:start -->
## 八、定量迭代实验：完整双版本代码

以下六个源文件与上述历史测量的输入逐字节相同。它们分别证明同一数学陈述；Litex 使用带条件函数，Lean 的结论限制在相同合法参数范围内。记录没有把底层函数在域外的不同约定当作相同机制。

数学设计和支持边界见 [math_collections.md](sources/quantitative-iteration/math_collections.md)。这里是单步公式与给定递推的证明，未声称已构造一般算法轨道或验证浮点舍入。

<a id="iteration-parametric-newton"></a>

### 1. 参数化 Newton 单步

任意 a>0、x>0 的正性、精确残差恒等式与更新后平方下界；在 a=9、x=4 上复用。

#### Litex

[源码](sources/quantitative-iteration/litex/01_parametric_newton.lit)；完整进程样本（秒）：`0.216478, 0.212586, 0.191081`。

```litex
# Exact-real comparison experiment; see ../math_collections.md.

have fn newton(a R+, x R+) R = (x + a / x) / 2

thm newton_positive:
    ? forall a, x R+:
        newton(a, x) > 0
    a / x > 0
    x + a / x > 0

thm newton_residual_identity:
    ? forall a, x R+:
        4 * x^2 * (newton(a, x)^2 - a) = (x^2 - a)^2

thm newton_above_root:
    ? forall a, x R+:
        newton(a, x)^2 >= a
    4 * x^2 > 0
    newton(a, x)^2 - a = (x^2 - a)^2 / (4 * x^2) >= 0

newton(9, 4) = (4 + 9 / 4) / 2 = 25 / 8

by thm newton_above_root(9, 4) => newton(9, 4)^2 >= 9
```

#### Lean / Mathlib

[源码](sources/quantitative-iteration/lean/01_parametric_newton.lean)；完整进程样本（秒）：`14.163907, 60.180296, 67.659174`。

```lean
import Mathlib
set_option Elab.async false

namespace ParametricNewton
noncomputable section

def newton (a x : ℝ) : ℝ := (x + a / x) / 2

theorem newton_positive {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    0 < newton a x := by
  unfold newton
  positivity

theorem newton_residual_identity {a x : ℝ} (_ha : 0 < a) (hx : 0 < x) :
    4 * x ^ 2 * (newton a x ^ 2 - a) = (x ^ 2 - a) ^ 2 := by
  unfold newton
  field_simp [ne_of_gt hx] <;> ring

theorem newton_above_root {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    a ≤ newton a x ^ 2 := by
  have hp : 0 < 4 * x ^ 2 := by positivity
  have hid : newton a x ^ 2 - a = (x ^ 2 - a) ^ 2 / (4 * x ^ 2) := by
    apply (eq_div_iff (ne_of_gt hp)).2
    calc
      (newton a x ^ 2 - a) * (4 * x ^ 2) =
          4 * x ^ 2 * (newton a x ^ 2 - a) := by ring
      _ = (x ^ 2 - a) ^ 2 := newton_residual_identity ha hx
  have hnonneg : 0 ≤ newton a x ^ 2 - a := by
    rw [hid]
    positivity
  linarith

example : newton 9 4 = 25 / 8 := by norm_num [newton]
example : (9 : ℝ) ≤ newton 9 4 ^ 2 :=
  newton_above_root (by norm_num) (by norm_num)

#print axioms newton_positive
#print axioms newton_residual_identity
#print axioms newton_above_root
end
end ParametricNewton
```

<a id="iteration-quadratic-descent"></a>

### 2. 二次函数梯度下降

一维正曲率二次函数的精确下降量、稳定步长下的不增性，以及离开最小点时的严格下降。

#### Litex

[源码](sources/quantitative-iteration/litex/02_quadratic_descent.lit)；完整进程样本（秒）：`2.880947, 2.905032, 2.952233`。

```litex
# Exact-real comparison experiment; see ../math_collections.md.

have fn energy(a R+, b, x R) R = a * (x - b)^2 / 2

have fn gradient_step(a R+, b, eta, x R) R = x - eta * a * (x - b)

thm gradient_error_identity:
    ? forall a R+, b, eta, x R:
        gradient_step(a, b, eta, x) - b = (1 - eta * a) * (x - b)

thm gradient_drop_identity:
    ? forall a R+, b, eta, x R:
        energy(a, b, x) - energy(a, b, gradient_step(a, b, eta, x)) = eta * a^2 * (2 - eta * a) * (x - b)^2 / 2
    energy(a, b, gradient_step(a, b, eta, x)) = a * (gradient_step(a, b, eta, x) - b)^2 / 2 = a * ((1 - eta * a) * (x - b))^2 / 2
    energy(a, b, x) - energy(a, b, gradient_step(a, b, eta, x)) = a * (x - b)^2 / 2 - a * ((1 - eta * a) * (x - b))^2 / 2 = eta * a^2 * (2 - eta * a) * (x - b)^2 / 2

thm gradient_descent:
    ? forall a R+, b, eta, x R:
        eta > 0
        eta * a < 2
        =>:
            energy(a, b, gradient_step(a, b, eta, x)) <= energy(a, b, x)
    eta * a^2 > 0
    eta * a^2 * (2 - eta * a) >= 0
    eta * a^2 * (2 - eta * a) * (x - b)^2 >= 0
    by thm gradient_drop_identity(a, b, eta, x) => energy(a, b, x) - energy(a, b, gradient_step(a, b, eta, x)) = eta * a^2 * (2 - eta * a) * (x - b)^2 / 2
    energy(a, b, x) - energy(a, b, gradient_step(a, b, eta, x)) >= 0

thm gradient_strict_descent:
    ? forall a R+, b, eta, x R:
        eta > 0
        eta * a < 2
        x != b
        =>:
            energy(a, b, gradient_step(a, b, eta, x)) < energy(a, b, x)
    x - b != 0
    eta * a^2 > 0
    eta * a^2 * (2 - eta * a) > 0
    eta * a^2 * (2 - eta * a) * (x - b)^2 > 0
    by thm gradient_drop_identity(a, b, eta, x) => energy(a, b, x) - energy(a, b, gradient_step(a, b, eta, x)) = eta * a^2 * (2 - eta * a) * (x - b)^2 / 2
    energy(a, b, x) - energy(a, b, gradient_step(a, b, eta, x)) > 0

by thm gradient_strict_descent(2, 3, 1 / 4, 5) => energy(2, 3, gradient_step(2, 3, 1 / 4, 5)) < energy(2, 3, 5)
```

#### Lean / Mathlib

[源码](sources/quantitative-iteration/lean/02_quadratic_descent.lean)；完整进程样本（秒）：`13.893024, 28.775592, 21.303137`。

```lean
import Mathlib
set_option Elab.async false

namespace QuadraticDescent
noncomputable section

def energy (a b x : ℝ) : ℝ := a * (x - b) ^ 2 / 2
def gradientStep (a b eta x : ℝ) : ℝ := x - eta * a * (x - b)

theorem gradient_error_identity {a b eta x : ℝ} (_ha : 0 < a) :
    gradientStep a b eta x - b = (1 - eta * a) * (x - b) := by
  dsimp [gradientStep]
  ring

theorem gradient_drop_identity {a b eta x : ℝ} (ha : 0 < a) :
    energy a b x - energy a b (gradientStep a b eta x) =
      eta * a ^ 2 * (2 - eta * a) * (x - b) ^ 2 / 2 := by
  unfold energy
  rw [gradient_error_identity ha]
  ring

theorem gradient_descent {a b eta x : ℝ} (ha : 0 < a)
    (heta : 0 < eta) (hstep : eta * a < 2) :
    energy a b (gradientStep a b eta x) ≤ energy a b x := by
  have hpos : 0 < 2 - eta * a := by linarith
  have hdrop : 0 ≤ eta * a ^ 2 * (2 - eta * a) * (x - b) ^ 2 / 2 := by
    positivity
  have hid := gradient_drop_identity (b := b) (eta := eta) (x := x) ha
  linarith

theorem gradient_strict_descent {a b eta x : ℝ} (ha : 0 < a)
    (heta : 0 < eta) (hstep : eta * a < 2) (hxb : x ≠ b) :
    energy a b (gradientStep a b eta x) < energy a b x := by
  have hpos : 0 < 2 - eta * a := by linarith
  have hne : x - b ≠ 0 := sub_ne_zero.mpr hxb
  have hdrop : 0 < eta * a ^ 2 * (2 - eta * a) * (x - b) ^ 2 / 2 := by
    positivity
  have hid := gradient_drop_identity (b := b) (eta := eta) (x := x) ha
  linarith

example : energy 2 3 (gradientStep 2 3 (1 / 4) 5) < energy 2 3 5 :=
  gradient_strict_descent (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms gradient_error_identity
#print axioms gradient_drop_identity
#print axioms gradient_descent
#print axioms gradient_strict_descent
end
end QuadraticDescent
```

<a id="iteration-perturbed-geometric"></a>

### 3. 含扰动的几何递推界

从给定的自然数索引实数序列及递推不等式出发，证明闭式上界并复用于零扰动；扰动项可为任意实数。

#### Litex

[源码](sources/quantitative-iteration/litex/03_perturbed_geometric.lit)；完整进程样本（秒）：`1.319137, 1.484209, 1.351820`。

```litex
# Exact-real comparison experiment; see ../math_collections.md.

forall q R:
    q < 1
    =>:
        1 - q > 0
        1 - q != 0

have fn bound(q R+, c, d R, n N: q < 1) R = q^n * c + d * (1 - q^n) / (1 - q)

thm bound_zero:
    ? forall q R+, c, d R:
        q < 1
        =>:
            bound(q, c, d, 0) = c
    1 - q != 0

thm bound_step:
    ? forall q R+, c, d R, n N:
        q < 1
        =>:
            bound(q, c, d, n + 1) = q * bound(q, c, d, n) + d
    1 - q != 0
    have t R+ = q^n
    q^(n + 1) = q^n * q^1 = t * q
    (t * q) * c + d * (1 - t * q) / (1 - q) = q * (t * c + d * (1 - t) / (1 - q)) + d
    bound(q, c, d, n + 1) = q * (t * c + d * (1 - t) / (1 - q)) + d = q * bound(q, c, d, n) + d

thm affine_recurrence_bound:
    ? forall err fn(idx N) R, q R+, d R, n N:
        q < 1
        forall j N:
            err(j + 1) <= q * err(j) + d
        =>:
            err(n) <= bound(q, err(0), d, n)
    by induc n from 0:
        ? err(n) <= bound(q, err(0), d, n)
        ? from n = 0:
            by thm bound_zero(q, err(0), d) => bound(q, err(0), d, 0) = err(0)
        ? induc:
            err(n + 1) <= q * err(n) + d <= q * bound(q, err(0), d, n) + d = bound(q, err(0), d, n + 1)

thm noiseless_affine_bound:
    ? forall err fn(idx N) R, q R+, n N:
        q < 1
        forall j N:
            err(j + 1) <= q * err(j)
        =>:
            err(n) <= q^n * err(0)
    claim:
        ? forall j N:
            err(j + 1) <= q * err(j) + 0
        q * err(j) + 0 = q * err(j)
    1 - q != 0
    bound(q, err(0), 0, n) = q^n * err(0) + 0 * (1 - q^n) / (1 - q) = q^n * err(0) + 0 = q^n * err(0)
```

#### Lean / Mathlib

[源码](sources/quantitative-iteration/lean/03_perturbed_geometric.lean)；完整进程样本（秒）：`13.798624, 36.547467, 17.129896`。

```lean
import Mathlib
set_option Elab.async false

namespace PerturbedGeometric
noncomputable section

def bound (q c d : ℝ) (n : ℕ) : ℝ :=
  q ^ n * c + d * (1 - q ^ n) / (1 - q)

theorem bound_zero {q c d : ℝ} (_hq0 : 0 < q) (_hq1 : q < 1) :
    bound q c d 0 = c := by
  simp [bound]

theorem bound_step {q c d : ℝ} (_hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    bound q c d (n + 1) = q * bound q c d n + d := by
  have hden : 1 - q ≠ 0 := by linarith
  dsimp [bound]
  rw [pow_succ]
  field_simp [hden] <;> ring

theorem affine_recurrence_bound (err : ℕ → ℝ) {q d : ℝ} (n : ℕ)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hrec : ∀ j, err (j + 1) ≤ q * err j + d) :
    err n ≤ bound q (err 0) d n := by
  induction n with
  | zero => simp [bound]
  | succ n ih =>
      calc
        err (n + 1) ≤ q * err n + d := hrec n
        _ ≤ q * bound q (err 0) d n + d :=
          by linarith [mul_le_mul_of_nonneg_left ih (le_of_lt hq0)]
        _ = bound q (err 0) d (n + 1) := (bound_step hq0 hq1 n).symm

theorem noiseless_affine_bound (err : ℕ → ℝ) {q : ℝ} (n : ℕ)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hrec : ∀ j, err (j + 1) ≤ q * err j) :
    err n ≤ q ^ n * err 0 := by
  have h := affine_recurrence_bound err n hq0 hq1 (d := 0)
    (fun j => by simpa using hrec j)
  simpa [bound] using h

#print axioms bound_zero
#print axioms bound_step
#print axioms affine_recurrence_bound
#print axioms noiseless_affine_bound
end
end PerturbedGeometric
```

这一批的六次正例验证、十二次预期拒绝检查和十八次重复正例检查均符合预期。零输入、错误残差、过大步长、最小点处严格下降、q=1、遗漏噪声项的控制保留在原始记录中。负例 fixture、平台二进制和本地工作日志没有作为此处的正例源码发布。

新副本可用 release Litex 的 `-strict -f <file>` 与配置好 Mathlib 的 `lake env lean <file>` 检查。既有 `harness/bench.py` 仍测其原来的检查路径用例，不将这三组完整进程记录混入旧的毫秒样本。

[搬入此目录后的路径验证](results/quantitative-iteration-promotion.json)：三份 Litex 副本另行通过记录版本二进制的严格检查；Lean 副本以相同源码哈希承接原先的成功检查，没有把路径验证冒充为新计时样本。
<!-- quantitative-iteration-code:end -->
