# Litex 到 Lean 的证明语句对应

2026-10-23 的证明流程验收包含下列实际生成的源码／Lean 对。编译器沿着 Litex 已执行的 WD、假设、证明、存储和推导记录生成证明；事实引用保留原 FactId，局部假设随原作用域关闭。生成定理保留显式的 `Litex.Semantics`、表示和所需集合／函数语义条件。

| 主题 | Litex 源码 | 编译生成的 Lean | 本轮接通的对应 |
| --- | --- | --- | --- |
| 复合反证 | [同时证明自反等式](../lean/examples/simultaneous_reflexive_equalities/statement.lit) | [Lean](../lean/examples/simultaneous_reflexive_equalities/statement.lean) | 消费实际记录的 `and`、`or`、chain 及混合命题的分类否定，再用原矛盾结论关闭反证。 |
| 集合中的反证和分类讨论 | [成员关系区分集合](../lean/examples/membership_distinguishes_sets/statement.lit) | [Lean](../lean/examples/membership_distinguishes_sets/statement.lean) | 非成员、非子集命题；原 union 成员推导得到的析取；每个 case 的局部假设。 |
| 集合外延 | [互为子集推出相等](../lean/examples/mutual_subset_equality/statement.lit) | [Lean](../lean/examples/mutual_subset_equality/statement.lean) | `by extension` 消费原来两个有方向的 subset 证明，再应用集合外延。 |
| 函数外延 | [相同的平移函数](../lean/examples/equal_shift_functions/statement.lit) | [Lean](../lean/examples/equal_shift_functions/statement.lean) | `by fn_extension` 消费完整定义域及逐点 forall；返回上界分别为 R、C 的同一函数也有检查例子。 |
| 强归纳 | [非负整数上的等式](../lean/examples/strong_integer_identity/statement.lit) | [Lean](../lean/examples/strong_integer_identity/statement.lean) | `by strong_induc` 保留原 base、step 和 `0 ≤ m ≤ n` 的有界归纳假设；导出的对象保持原表示。 |
| 有限枚举 | [有限域上的平方与二元取值](../lean/examples/finite_square_values/statement.lit) | [Lean](../lean/examples/finite_square_values/statement.lean) | `by for` 和 `by enumerate finite_set` 消费全部原赋值；覆盖普通分支、已证伪前提、空域和定理内局部枚举。 |
| 几何中的坐标构造 | [中点到两端等距](../lean/examples/midpoint_equidistance/statement.lit) | [Lean](../lean/examples/midpoint_equidistance/statement.lean) | 缓存命中仍定位原 Cartesian 坐标发布记录；复用其对象和成员证据，保留原有限坐标展开及标量计算。 |

## 与 Litex 执行流程的关系

反证先引入记录中的反向假设，在该局部环境中完成证明，再关闭环境、存储原目标。编译器验证否定的分支、次序和对象，与原记录一致后才使用固定的逻辑变换。集合外延同样保留两个 subset 方向；函数外延同时检查完整定义域和逐点相等。

有限枚举按记录中的赋值次序逐支编译，并从原显式列表的成员关系证明覆盖性。跳过分支需要该分支实际返回的前提否定证明。赋值等式通过语义值上的合同性运输原前提和结论；分支事实只能由相应的原作用域和已完成前缀引用。

已形成的坐标可能在后续 WD 中只剩一个缓存编号。此时复用原发布位置的构造，而不是把后来碰到的同形推导当成构造来源。集合描述中的函数表达式则消费原条件 WD，以原绑定变量和更早条件的投影组成局部构造工厂。这些证据保证域、条件和声明含义在编译后保持一致。

## 当前边界

- 复合反证覆盖受支持的量词自由 atomic／and／or／chain 形状；量词否定仍有独立缺口。
- 强归纳的本轮桥接从零开始，保留原整数域和非负条件。
- 函数外延目前支持单参数、α 等价的完整定义域，来源为已有成员引用或匿名函数；`R+` 参数、非 α 等价的定义域比较及其他来源仍显式拒绝。
- 有限枚举支持显式列表、`range`／`closed_range` 及其多参数组合，见[矩形平方和](../lean/examples/integer_rectangle_square_bound/statement.lit)。保留完整赋值顺序和 1,024 组合上限；依赖前面参数的枚举域仍显式拒绝。
- 这些是编译器覆盖边界，超出边界的输入会拒绝整个生成产物。

## 本轮验收

完整编译器 Rust 回归：`cargo test --lib compile_to_lean`，740 通过、0 失败。针对破坏或删掉原假设、改变分支／赋值次序、改写目标或成员证据、引用未来或其他分支事实的检查均保留。调用内部的 selected-proof WD 与返回调用者后的 WD 分别检查。

实际 CLI 生成的 11 对源码／Lean 通过固定 Lean 4.31.0 与 Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` 检查，审计 100 个生成声明。除上表七对外，还复验了 [直线成员条件](../lean/examples/line_membership_condition/statement.lit)、[平方集合成员](../lean/examples/square_set_membership/statement.lit)、[偏移分母的分配律](../lean/examples/shifted_guarded_quotient_distribution/statement.lit) 和 [Newton 误差上界](../lean/examples/newton_residual_bound/statement.lit)。这四个先前的编译卡点均已通过。

公理审计仅出现 `Classical.choice`、`Quot.sound` 和 `propext`。验收固定了编译器及 Core 快照，避免同一工作区的并行改动混入检查记录；这些检查工具和收据保存在本地 scripts 工作区。此次没有宣称跨独立源码运行的 FactId 字节稳定性，也没有把这一批次当作整个 Litex 语言或整个 Geo 的覆盖证明。
