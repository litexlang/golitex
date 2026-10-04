> 2026-10-04用户更新：成功的 `eval` 现在核验并发布 `source = result`。下文关于 display-only／不存事实的旧决定属于历史，现行合同见[Manual](../../docs/Manual.md)与[验收经验](experience/problem_notes/eval_store_result_2026-10-04.md)。

# 数值、虚数单位与 sum/product 能力恢复计划

## 任务与证据边界

- 用户要求：修复十进制规范化；把 `i != 0` 做成 builtin rule；强化 `sum` 与 `product`；先对照 legacy 制定计划。
- 日期：2026-10-02。实现工作区：golitex；验收与问题记录：`examples/test_objs`。
- 本文件保留实施前的源码对照和验收计划。用户后续批准四阶段实现及选项 A；现已实现，当前结果见 [验收记录](acceptance.md)。下文标为“当前”的缺陷描述指制定计划时的基线，不代表修复后的状态。
- 当前执行证据来自 [诊断记录](diagnosis_2026-10-02.md) 及 [带源码/二进制哈希的 journal](proof_journals/diagnosis_2026-10-02.json)。本轮没有重新构建或执行 legacy。
- legacy 对照基线：commit `8ebce3f7a4a4c61250063c9eb9e69c9fb3cfa735`。下列六个归档文件逐字节与该 commit 的对应 `src/` 文件一致，已用 `git show` 独立检查：`object/numeric_constants.rs`、`verification/builtin_rules/complex_builtin.rs`、`execution/command_execution/evaluation.rs`、`verification/builtin_rules/equality_numeric/{iterated_ranges,finite_set_sum,finite_set_product}.rs`。

## 已确认的实现差异

| 能力 | legacy 源码事实 | 当前源码与已有运行证据 | 分类 |
| --- | --- | --- | --- |
| 数值构造规范化 | `Number::new` 调用 `normalize_decimal_number_string` | `Number::new` 只存字符串；parser 直接构造 Number。等值小数等式拒绝，反向不等式错误接受 | 迁移遗漏，并造成当前实现缺陷 |
| 虚数单位非零 | `try_verify_native_i_nonzero` 直接匹配 `i != 0` 与 `0 != i` | 当前 `!=` builtin 没有对应叶规则；直接 `i != 0` 失败 | 迁移遗漏 |
| 有限范围求值 | `eval_sum_or_product_for_eval_stmt` 计算整数上下界，逐项绑定代入、递归化简嵌套聚合、累加/累乘 | 当前 eval dispatcher 没有 Sum/Product 分支，返回 `unsupported_expression` | 求值能力迁移遗漏 |
| 符号聚合规律 | legacy 有区间分拆、求和逐点相等/线性/常数/平移等规则；有限集合有单独规则族 | 当前已有单项、拆最后项、列表集合展开与部分集合规则；尚缺完整对应范围规则 | 分项对照后恢复，不能说整个规则族都缺失 |
| eval 的事实发布 | legacy `exec_eval_stmt` 构造并存储源对象等于结果的事实 | 当前 `exec_eval_stmt` 明确只展示结果，已有 no-facts 边界测试 | 当前公开行为差异；不能仅因旧版会存储便自动改回 |

legacy 的求值实现可以指导恢复能力，但不是整文件复制目标：它的 range eval 只接受一元匿名函数，以 `i128` 解析界限，直接遍历范围，没有这里所需的跨嵌套总工作量预算。具名函数、受控预算和新的成功证据必须与当前机制对齐。

源码锚点：

- [legacy Number 构造器](../../scripts/memorial_legacy_src/object/numeric_constants.rs:19)。
- [legacy 虚数单位非零](../../scripts/memorial_legacy_src/verification/builtin_rules/complex_builtin.rs:121)。
- [legacy range eval](../../scripts/memorial_legacy_src/execution/command_execution/evaluation.rs:320)。
- [legacy eval 存事实](../../scripts/memorial_legacy_src/execution/command_execution/evaluation.rs:1851)。
- [legacy 区间聚合规则](../../scripts/memorial_legacy_src/verification/builtin_rules/equality_numeric/iterated_ranges.rs)。
- [legacy 有限集合求和](../../scripts/memorial_legacy_src/verification/builtin_rules/equality_numeric/finite_set_sum.rs) 与 [求积](../../scripts/memorial_legacy_src/verification/builtin_rules/equality_numeric/finite_set_product.rs)。

## 先固定的数学不变量与职责

1. 十进制字面量表示精确数值；等值的不同拼写必须具有一致的内部数值和比较结果。验证合法文本后规范化，不经浮点转换。
2. 内建 `i` 是专用 ImaginaryUnit AST 常量，非零是它自身的性质；普通复数变量不能只凭属于 `C` 就被判非零。
3. 除法合法性仍要证明分母非零。复数恒等式化简必须消费这些证据，不能删除 guard。
4. 闭整数区间聚合先确认端点为整数、start<=end、一元函数、返回值属于数值 carrier，且整个区间包含在函数定义域内。
5. 每个合法指标先代入函数体，再化简该项；求和使用 +，求积使用 *。替换由现有 IdentifierId/绑定身份机制完成，不使用变量文本替换。
6. 当前 range sum/product 的逆向区间仍拒绝；有限集合空求和为 0，空求积为 1。它们是不同输入接口的既有契约。
7. 同一展开/计算机制服务显示与验证；事实是否发布由原有命令/验证入口决定。Failed、预算耗尽与 unsupported 均不能成为等式成功证据。

对应职责：Number 构造与 decoder 保证规范化；WD 负责载体/定义域；现有 instantiate 和函数展开负责代入；聚合计算负责逐项遍历与 fold；验证器负责等式证据；eval 负责展示。计划不需要新增 Obj/Stmt/Fact 字段或 Env/Runtime 状态字段。

## 第一阶段：恢复规范化，先堵错误接受

现有问题及拟验收结果：

```litex
2.400 = 2.4       # 当前拒绝；修复后应通过
2.400 != 2.4      # 当前错误通过；修复后必须拒绝，独立 negative fixture
2.400 - 2.4 = 0   # 已通过的控制，应继续通过
2.000 = 2        # 拟验收
0.000 = 0        # 拟验收
(-0.000) = 0     # 拟验收
0.1 + 0.2 = 0.3  # 原有精确计算回归
```

实施顺序：

1. 恢复现有 `Number::new` 的精确规范化，不改变 Number 的字段形状。
2. parser 合法性检查之后走该构造器，消除绕过入口。
3. 审计 `number_from_normalized`、KB 数值 decoder 和其他直接构造处，避免只修新解析对象而旧对象仍不规范。
4. 验证等式、不等式、大小比较、整数判断、numeric IR key、序列化/载入一致。若旧缓存需要迁移/失效，先提出其现有版本契约下的具体方案，不能默默修改 Runtime/Env 的状态契约。
5. 将已有 P03 提升为正常正例，N03 转为正确拒绝的反例；只在实际验证后更新 gap/baseline/todo。

主要文件：[numeric helper](../../src/rational_expression/helper.rs)、[parser](../../src/parse/object/primary.rs:809)、[numeric evaluator](../../src/rational_expression/decimal_arithmetic.rs)、[KB decoder](../../src/knowledge_base/def_prop_codec.rs)。

## 第二阶段：恢复 i 非零 builtin，并接通复数除法

用户已确定的行为：直接 builtin 证明非零，不要求作者手写反证。

```litex
i != 0             # 应直接通过 builtin
0 != i             # legacy 同时支持另一朝向
i $in C*           # 检查非零事实与 refined membership 的组合
1 / i = -i         # 完整链路验收
```

独立反例：

```litex
i = 0              # 必须拒绝
1 / i = -1         # 必须拒绝
let bad = 1 / (i - i)  # 必须在 WD 拒绝
```

实施顺序：

1. 在当前 `!=` builtin owner 增加专用 `ImaginaryUnitNonzero` 规则和成功证据，只匹配内建常量与数值零，支持两种朝向。
2. 接好 proof method 与 Normal/Detailed 输出，验证除法 WD 可以消费该规则，不仅在顶层测试它。
3. 补齐已有复数化简在“有非零分母证据”场景的入口。当前 `Calculation::Complex` 只准实数十进制求值器可算出的非零分母；guarded rational strategy 又不使用 `i²=-1`。必须连同这条链路恢复，不能以单独 `i != 0` 通过宣布 inverse 已修。
4. 纯闭合计算继续作为计算叶；需要验证非零前提的复数化简走带前提的策略，保留每个分母证据及既有搜索预算。
5. 检查复合分母、乘法/平方和、导入及别名中的专用常量，不把任何名字像 `i` 的普通标识符当内建常量。

主要文件：[not-equal builtin](../../src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/search_atomic_except_equality_fact_proof_by_builtin_rules/not_equal.rs)、[division WD](../../src/execute/execute_fact_stmt/well_defined_results/verify_obj/scalar.rs:88)、[calculation guard](../../src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/verify_equality_by_builtin_rules/search_equal_fact_by_calculation.rs:43)、[guarded rational strategy](../../src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/search_equal_fact_by_rational_with_nonzero_premises.rs)。

原反证写法的重复运行不稳定现象仍保留在诊断 journal；恢复 builtin 后不依赖该绕路，也不宣称它的独立根因已修复。

## 第三阶段：sum/product 的逐项展开与精确求值

首批直接目标：

```litex
sum(1, 3, fn(k Z) Z {k}) = 6
product(1, 3, fn(k Z) Z {k}) = 6
sum(-2, 2, fn(k Z) Z {k * k}) = 10
product(-2, 2, fn(k Z) Z {k}) = 0
sum(1, 3, fn(k Z) Q {1 / 3}) = 1

eval sum(1, 3, fn(k Z) Z {k})      # evaluated_object 应为 6
eval product(1, 3, fn(k Z) Z {k})  # evaluated_object 应为 6
```

单项、求和/求积和四则组合都使用相同机制，例如拟验收：

```litex
sum(1, 3, fn(k Z) Z {k}) + product(1, 3, fn(k Z) Z {k}) = 12
sum(1, 3, fn(k N+) N+ {product(1, k, fn(j N+) N+ {j})}) = 9
```

建议的小流水线：

```text
原表达式 WD
  -> 根据已证明相等关系解析有限整数上下界
  -> 枚举指标；复用 IdentifierId 绑定与现有 inst_obj 代入
  -> 验证函数应用的 domain；展开函数体
  -> 递归处理该项中的 sum/product 与支持的精确计算
  -> 以 0/+ 或 1/* 累积
  -> 返回结果与原聚合等于结果的成功证据
```

两个分支各自拥有 Sum/Product 证据，低层代入与算术 fold 可复用。新增非平凡流水线结果按阶段顺序组织；证据保留被使用的已知 FactId、指标代入、每项计算、最终累积与必要局部环境。遵循 `litex-pipeline-result-types`，不把失败装进成功 Proof，也不新增只转发/改名的框架层。

执行次序：

1. 在现有 `execute_eval_stmt/evaluate_obj` 与 equality owner 之间落实共同的、有证据的聚合展开操作；纯数值算术继续复用 `rational_expression`。
2. 先迁回 legacy 的一元匿名函数范围迭代；严格验证所有应用条件。
3. 补齐嵌套 sum、嵌套 product、交叉嵌套与外层四则组合。不能只识别最外层的两个例子。
4. 复用当前函数定义展开入口接入有可执行定义的具名函数/别名；明确这是相对 legacy range eval 仅接受匿名函数的扩展。声明为函数但没有可执行定义，不等于可以算出数值。
5. 接入已有可支持的 algo 调用；不让任意循环/递归成为数值证明。
6. 两个 consumer 接线：eval 展示 evaluated_object；直接等式验证检查展开/计算证据。验证 `sum(...) = 7`、`product(...) = 7` 始终拒绝。
7. 增加总工作量预算，跨嵌套共同消耗，不给每个内层循环重新获得全额预算。端点差值和指标推进做 checked 运算；超界、无法计算或预算耗尽明确失败且无事实泄漏。预算具体数值由 focused 性能/资源测量确定，不在计划中凭空固定。

具名函数拟验收：

```litex
have fn square(k Z) Z = k * k
sum(1, 3, square) = 14
product(1, 3, square) = 36
```

当函数体含不能精确化简的项时，不把近似数值写成等式证明。符号上界的行为由下一阶段的数学规则完成，有限遍历不是所有数学事实的替代品。

## 第四阶段：恢复符号规则与有限集合接口

按 legacy 对照表逐项迁移，当前已存在的规则先检验连通性，不重复添加。下面是拟验收的代表性规则形状，均需要合法载体、定义域和区间条件：

| 规则族 | 代表性代码形状 | legacy 锚点 / 当前状态 |
| --- | --- | --- |
| 常数求和 | `sum(a, b, fn(k Z) R {c}) = (b - a + 1) * c` | legacy `try_verify_sum_constant_summand`；当前需恢复 |
| 求和加法与减法 | `sum(a,b,fn(k Z) R {f(k)+g(k)}) = sum(a,b,f)+sum(a,b,g)` | legacy additivity/subtraction；当前需恢复并检查共同 additive carrier |
| 标量提出 | `sum(a,b,fn(k Z) R {c*f(k)}) = c*sum(a,b,f)` | legacy scalar_mul；当前需恢复 |
| 逐点相等 | `sum(a,b,f) = sum(a,b,g)`，前提为区间内 `f(k)=g(k)` | legacy pointwise congruence；现有 alpha 同一性不是这条数学定理 |
| 区间分拆 | `sum(a,b,f) = sum(a,c,f)+sum(c+1,b,f)`；product 以乘法组合 | legacy partition；保留合法子区间条件 |
| 平移重编号 | `sum(a,b,fn(k Z) R {f(k+t)}) = sum(a+t,b+t,f)` | legacy reindex_shift；保留整数平移及函数覆盖 |
| 集合与 range 桥 | `finite_set_sum(closed_range(a,b),f) = sum(a,b,f)`；product 同理 | legacy 有两套桥；空 range 不能偷换契约 |
| 集合常量 / 逐点 / 合并 | `finite_set_sum(S,fn(k S) R {c}) = finite_set_size(S)*c`；求积对应常量因子和逐点/乘法规律 | legacy finite_set_sum/product 专属族；逐项审查现有迁移 |

例如符号上界的完整拟验收：

```litex
forall n N+, c R:
    sum(1, n, fn(k Z) R {c}) = n * c
```

有限集合求值先覆盖可枚举的显式列表集合与整数 range；一般有限集通过已证明的枚举/数学规则处理，不能仅凭“finite_set”就假设拥有全部元素。

```litex
finite_set_sum({1, 2, 3}, fn(k Z) Z {k}) = 6
finite_set_product({1, 2, 3}, fn(k Z) Z {k}) = 6
finite_set_sum({}, fn(k Z) Z {k}) = 0
finite_set_product({}, fn(k Z) Z {k}) = 1
```

扩充前同步堵住已记录的 domain 漏洞；以下原样输入必须拒绝，不能因为可代入计算就忽略声明的定义域：

```litex
let bad_sum = finite_set_sum({1}, fn(k {2}) Z {k})
let bad_product = finite_set_product({1}, fn(k {2}) Z {k})
```

有限集合域覆盖应由现有 WD owner 保证，再由计算 consumer 检查/使用；既有 Fubini/Cartesian-product 求和规则只审计其证据与组合，不借这次修改重新打开旧版其他已移除接口。

## 明确列出的行为选择：eval 是否发布等式

共同目标是支持同一个合法表达式得到精确结果，并让下面直接断言通过：

```litex
sum(1, 3, fn(k Z) Z {k}) = 6
```

选项 A（建议）：保持当前 display-only eval；直接等式验证消费新的聚合计算证据。

```litex
eval sum(1, 3, fn(k Z) Z {k})
# 拟输出：evaluated_object = 6；stores = []
```

收益：符合当前 Manual 与 `evaluation-exports-no-facts` 测试；计算证据可共用；不改变命令的事实发布契约。代价：单独 eval 不会让一个昂贵等式成为可复用的已存事实；后续直接断言可能需要再验证计算。

选项 B：恢复 legacy 的成功 eval 发布等式，必须有完整证明证据后再存储/推导。

```litex
eval sum(1, 3, fn(k Z) Z {k})
# 拟输出：evaluated_object = 6
# stores = ["sum(1, 3, fn(k Z) Z {k}) = 6"]
```

收益：保留 legacy 作者通过 eval 建立后续事实的工作方式，结果可被后续已知事实路径复用。代价：改变当前命令/publication 行为、输出和 no-facts 验收；需要审查 Facts 的状态管理契约与事务边界，若涉及受保护 Env/Runtime 合同则须另列具体变更。切换影响已有脚本与后续证明依赖，不能隐藏在 evaluator 迁移里。

两种选项都能增强 sum/product；差异是计算命令的语义和事实生命周期。用户已批准并实现 A：eval 展示精确值，直接等式保存验证证据。无限和/积、新求和语法、改变空 range 定义、重做反证搜索不属于这四阶段。

## 验收与实施门禁

每阶段先写正例与最近反例，再按顺序实现与执行。验收代码保留在 feature-owned examples；`test_objs` 继续按每个 Obj 保存多样测试、gap/todo 与 journal。任何新可用能力不能只留在临时 probe。

| 阶段 | 影响等级初判 | 必须验证的 owner / 边界 |
| --- | --- | --- |
| Number 规范化 | L3：共享数值构造/消费契约 | parser、decoder、精确运算、=/!=/比较/整数 membership、冷/热读取和键一致性 |
| i builtin | 叶规则及其证据输出 L2；复数非零策略 L3 | 正负朝向、division WD、复数化简、JSON proof route、无非零前提不得抵消 |
| range 求值 | L3：展开 producer 与 eval/equality consumer | 代入/domain、嵌套/具名函数、精确分数、proof output、工作量预算与失败回滚 |
| 符号/集合规则 | L2 规则族；WD 共享检查按实际 fan-out 调整 | 原 legacy 前提、集合域覆盖、常量/线性/逐点/分拆/重编号与错误边界 |

拟执行的当前 CLI 门禁：

```sh
cargo build --release
python3 examples/test_objs/run.py --object number
python3 examples/test_objs/run.py --object imaginary_unit --object div
python3 examples/test_objs/run.py --object sum --object product
python3 examples/test_objs/run.py --object sum_of_finite_set --object product_of_finite_set
python3 examples/test_objs/run.py --audit-only
python3 examples/test_objs/test_runner.py
```

这些 intended gates 包含其他已有 gap；实施时先列本阶段覆盖哪些 fixture，剩余失败逐项报告，不能把 known-gap baseline 通过当作修复完成，也不能为了全绿删除无关问题。

聚合端点、预算、闭合数值 fold 与引用证据分别加真实 Rust regression，入口仍只调用 `Runtime::exec_stmt`；现有 `exec_eval_stmt_tests`、`equality_search`、`builtin_entry_policy`、`statement_boundaries`、KB/json suites 按修改 owner 选 release filter。新的 filter 在 wiring 之后用 `--list` 确认实际收集，再执行，不能依靠零测试通过。端点溢出与跨嵌套预算必须覆盖。

首个 feature `.lit` 跑通后，再执行直接受影响的旧 examples 和 docs snippets。数字构造的共享影响或新 proof route 需更新 Manual、FAQ、架构说明与 Normal/Detailed 输出；保存已知旧失败、当前活跃写法及独立 negative。完整 corpus 最终重跑一次作为迁移影响检查，仍如实保留不在本计划内的未解决项。

Lean 编译能力与当前 verifier 成功是独立完成条件。如果实现确实修改到编译器消费的证据契约，再按其真实 owner 选择对应 Lean 门禁；本轮计划不声称这些新规则已有 Lean export。

## 建议执行顺序与完成定义

按 **Number 规范化 → i builtin 与复数除法链路 → 有限 range 求值及嵌套 → 符号规则和有限集合接口** 执行。定义域检查作为计算启用的前置条件，与所属阶段一起修复。

每片完成必须满足：原样正确例子通过、最近错误例子拒绝、退出码与 JSON success 一致、成功证据可追溯、失败不发布事实、实际收集的 focused tests 通过、现有 gap/todo 只按已验证结果更新。实施结果、原始失败与仍需显式前提的边界保存在当前验收和 journal 中；旧 baseline 报告保留为历史证据。
