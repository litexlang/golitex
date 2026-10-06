# 精确属性的结构查找契约（2026-10-06）

用户批准：函数签名、函数体、返回载体、完整 domain、坐标和类似结构信息，只读声明及精确对象的 special_properties；不搜索等价类，也不沿相等对象递归读取属性。需要的信息先经过证明/现有推导发布到实际使用对象上。普通等式、已知事实匹配和数学规则的证明仍保留各自的相等证据路线。

## 直接证据与明确边界

```litex
have fn step(x R) R = x + 1
let first = step
let second = first
# second(3) = 4 现在在 WD 阶段拒绝：没有本对象的函数签名。
second = fn(x R) R {x + 1}
second(3) = 4
```

发布的等式可由普通相等证明建立；函数查找随后只读取 second 上的直接 Equality。签名成员关系只提供调用类型，不提供具体函数体。已有 Equality、Membership、DefaultStructView 足够；没有新增 property variant、Env/Runtime 状态、AST 字段、缓存或 alias closure。现有 KnownEqualityPathProof 在结构读取中只承载 0/1 条直接引用，不代表执行等价图搜索。

```litex
have Base set = finite_seq(R, 2)
have Alias set = Base
Alias = finite_seq(R, 2)
have f Alias
f(2) $in R
```

需要完整载体时，在引入成员之前发布 Alias 的端点。没有该端点，成员声明可能成立，但调用无法取得完整签名。有限集合枚举也遵循此限制：`let Alias = Base` 后 `eval finite_set_sum(Alias, ...)` 不再遍历 Base 的等价类寻找集合显示；先证明 `Alias = {1, 2}` 后可以枚举。

## 已实现的 owner

14 个 Rust 文件覆盖：公共精确属性读取、函数 WD/签名、普通与 parent-checked 函数体展开、template body、codomain/标准上界、完整 domain/返回载体、有限函数坐标、载体成员推导、set builder/幂集/subset 结构投影，以及 eval 有限集合枚举。各消费者不再调用 visible_equivalence_class_adjacency、equivalence_class_keys/path 或相等连通分量枚举。构图仍属于普通证明的相等证据消费，不用于这些结构发现。

持久 tracer：[exact_property_function_lookup.lit](../../../proof_nodes/equal/by_object_definition/by_fn_application/exact_property_function_lookup.lit)。原隐式作者路线保留在注释中；活动代码覆盖声明、显式 body/签名、模板别名、载体端点、坐标及集合枚举。Rust 边界验证 transitive lookup 拒绝、两种等式方向、实际 FactId、失败不发布、错误值/参数、模板约束和没有函数体的签名。

受影响作者代码通过显式已证明的成员关系、函数体或 tuple/application 端点迁移，没有新增 trust。N23 保持有效前缀后在原错误数值 5 上拒绝；载体别名的越界负例另有 f(2) 接受/f(3) 拒绝控制，避免缺签名掩盖越界。

## 验证与限制

- Frozen release 和工作区 target/release/litex 相同：SHA256 `143607bea4ae0f1fb36e60e306bb9cfc680cfab29873eb7693d54ca77a9c4412`。
- 函数集合正式回归 85/85（58 正、27 负），成功前缀和预期失败阶段保持；10 个原始片段继续作为观测，CAP_T05 直接接受，其余 9 个不作为数学负例。CAP_T03 的首个失败仍为绑定，随后引用未定义 f 导致 parse session_error，不能将后续错误当作首因。
- 直接受影响的 47 个实际 `.lit` 文件严格模式全部接受；修改的 5 个规范文档片段通过。
- 第一轮收紧后的重点 Rust 84 个通过；最终精确属性 3 个通过、run_examples 的 12 个通过。最后完整 lib 审计为 1037 通过、10 失败，不能称整个 Rust 库全绿。
- 剩余 10 个是已有 tuple/cart 退役语法测试：example_small_finite_eval、direct_structural_membership 的两个测试、showcase_local_rules 的三个测试、predicate_domain_wd 的 dimension 测试、builtin_entry_policy 的三个测试。冻结旧二进制同样拒绝 tuple_dim/cart_dim、`[]` 和 literal tuple call；没有为这些测试恢复退役接口。完整测试名和旧版控制保留在回执。
- 并行任务的 real-power/log 更新曾短暂造成编译/测试中间态；本任务未修改其 scalar.rs、AST 注释或数学规则。最终构建已成功，单独 real-power 检查通过；这些中间态不归因于本次查找限制。
- 未运行 Lean/教材/完整发布门禁，也未进行性能基准；只确认结构读取已移除全图构建与遍历。普通证明仍可能使用相等图，不能据此声称系统完全不再构图。

机器回执：[最终门禁](../../../../plan/迁移的plan/proof_journals/exact-property-structural-lookup-gates-2026-10-06.json)，[持久会话作者迁移记录](../../../../plan/迁移的plan/proof_journals/exact-property-structural-lookup-2026-10-06.json)。原始日志、旧/新二进制、源码快照和脚本保留在 `tmp/2026-10-06/exact-property-structural-lookup/`；已完成 SOP 内容归档到回执，根执行 ledger 在完成审计后删除。
