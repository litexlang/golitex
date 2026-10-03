# Examples 小项修复验收（2026-10-02）

用户授权“先把小问题全部修理”。本批完成总计划中的 22 张能力卡：A01/A02、B01，
legacy BT02/03/07/10–13/20/23/26、IF01–05、WD01、EX02–04。
没有新增 trust、假设、axiom、弱化数学目标、扩大搜索预算，或修改受保护 AST/Env/Runtime/state 结构。
源码有并发工作，下面区分本批实现和最终共享快照的行为；这是定向验收，不是全仓验收。

| owner / 结果 | 证据与边界 |
| --- | --- |
| N+ membership | 消费 `k in Z` 和 `k>0` 两份证明；[原通式、前驱和 countdown](proof_nodes/atomic/by_builtin_rule/positive_integer_in_npos.lit)六条语句严格通过。整数/正性缺失、零、负数和分数拒绝 |
| scalar equality / inequality | 非零差/和推不等、abs 零、floor/ceil 取负与整数平移、min/max 吸收、lcm 零、非零复数模非零；独立 proof struct、Normal 说明、Detailed 子证明；未放宽 constructor WD |
| exact integer range-builder | 半开与闭区间分别有 proof/result；检查 Z 基域、两条精确边界，不吞掉额外谓词，空/逆序区间也验收 |
| finite surjection | 有限源 + 满射推出目标有限；保留源 FactId 和有限源证明，不以 injective 替代 surjective |
| canonical definition inference | prime、coprime、proper subset/superset、dvd、bijective 消费同一现有定义，发布的证据引用源 FactId。coprime 非全零保留为整个析取；gcd(0,0) 及错误 dvd 方向拒绝 |
| scalar carrier | floor/ceil、min/max、fold 已检查返回集合；整数取负/abs/+/-/* 检查 operand 证明；直接匿名函数调用读取已验证的静态 scalar ret_set，未开放整数除法、错误函数体或不匹配实参 |
| finite literal eval | size、合法 tuple 维数/投影、非空有限实数 extrema；分数按精确有理差比较，不转浮点。eval 不发布 equality；互异性/空/nonreal/域外 index 检查保留 |
| diagnostics | cases 的 coverage/disjoint/body WD/返回类型，Normal/Detailed 输出已有阶段、从 1 起始的分支和嵌套证据；普通 fact WD 展示已有树。生产者未保存原目标时仍可能出现 `<wd_failed>`；claim 第 5 项未实施 |
| proof migration | [匿名函数 equality](proof_nodes/equal/by_builtin_rule/anonymous_function_beta_extension.lit)改普通 equality + fn_extension，strict 通过。B06 singleton 与归纳步非空证明补 contra；整文件后续 obligation 保留 |

复跑本批实现：

```sh
cargo build --release
cargo test --release example_small_
target/release/litex -strict -f examples/example_small_repairs.lit
target/release/litex -strict -f examples/proof_nodes/atomic/by_builtin_rule/positive_integer_in_npos.lit
target/release/litex -strict -f examples/proof_nodes/equal/by_builtin_rule/anonymous_function_beta_extension.lit
```

每个正例文件要求 exit 0、JSON `kind: run` / `success: true`、所有语句成功且 `session_error: null`。
[13 个负例](negative/example_small_repairs)要求 exit 1、`success: false`、无 session/parse error，
并且存在具体失败语句；超时或 launch 错误不算正确拒绝。

最终验收：78 个定向 CLI 输入，74 个符合目标，无崩溃/超时；六个正例整文件全部通过，
13 个新增负例全部符合预期；8 个新增 Rust 测试通过，相邻回归去重合计 57 个全通过。
8 个连续 session 块检查源顺序、Normal/Detailed 证据、失败后继续和局部假设不泄漏。
构建与测试均为 release；共享 target 长时间锁住后，使用本任务独立 CARGO_TARGET_DIR 完成验收。
完整 code、命令、stdout/stderr、envelope、源码 hash、原片段与失败尝试见
[实施 journal](../plan/迁移的plan/proof_journals/example-small-repairs.json)。

无序 fold 的 AC 守卫由并发工作接入，本批没有删掉它。最初自己的 guard 候选因匿名嵌套调用超时而撤回，
证据和代码只留 journal；后来补直接匿名调用的 scalar 返回 carrier 后，最终加法/乘法 WD 通过，
无序减法正常拒绝、有序减法通过。最终所选 fold 计算等额外能力也由并发工作修复，不计为本批代码贡献。

仍开放的四个探针：

- 嵌套 tuple：`eval ((1,2),3)[1][2]` 在求值前的 shape/WD 失败。未把它换成一层投影。
- B06：singleton 定理现在通过。归纳步非空证明通过后，前驱索引函数存在目标 WD 通过、search 失败；显式 by def 原性质仍失败。保留原完整归纳/函数目标。
- opaque 积分样式：首个 equality 单独严格通过；完整文件的 anonymous integrable theorem 实例化仍失败，命名负函数后 integral equality 仍失败。旧前提和最终 trust 债务保持明确未完成，没有改成 axiom 或把带 trust 的文件算已证明。
- output trace：普通模式第 66 行旧 inline trust 语法失败，strict 先禁止 abstract_prop；尚有旧 register/choice 接口和数学建模债务，不只做 trust 语法替换。

验收结束后，共享工作区又有并发 existence 验证/证据源码变化；路径、后续源码及哈希已记入新 journal。
本页验收结果属于已经冻结的 release，不能当作这些后续改动也已通过本批 gate。

当前入口为 [总计划 §0](../plan/迁移的plan/example总问题与执行计划.md) 和
[迁移索引](../plan/迁移的plan/和example有关.md)。原 77/43 数量属于实施前快照，本批没有全量重扫，不能从它们机械减数。
