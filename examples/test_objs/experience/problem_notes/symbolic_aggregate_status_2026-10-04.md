# 符号聚合 R04/R05/R06 现状 — 2026-10-04

用户要求查看这三类旧失败。重新冻结 production 源码并构建 release，十个原短输入分别运行：七个直接通过，三个仍在 search_proof 拒绝。既有显式证明的五个完整文件全部严格通过。本次没有改 Rust 或证明代码。

| 原项 | 原短输入 | 当前直接结果 | 数学目标的显式证明 |
| --- | --- | --- | --- |
| R04 | 常量区间 sum | search_proof 失败 | 归纳通过 |
| R04 | 区间 sum 加法 | 通过 | 原作者文件通过 |
| R04 | 区间 sum 减法 | 通过 | 原作者文件通过 |
| R04 | 区间 sum 常数倍 | 通过 | 原作者文件通过 |
| R04 | k+k / 2*k 点态替换 | search_proof 失败 | 函数外延后替换通过 |
| R05 | 常量区间 product | search_proof 失败 | 归纳通过，保持 n N+、c R* |
| R06 | 有限集 sum 加法 | 通过 | 原作者文件通过 |
| R06 | 有限集 sum 减法 | 通过 | 原作者文件通过 |
| R06 | 有限集 sum 常数倍 | 通过 | 原作者文件通过 |
| R06 | 有限集 product 点态乘法 | 通过 | 原作者文件通过 |

这些是含未知 n、S、f、g 的恒等式，不是枚举数值的 eval。成功 eval 的结果发布并不自动解决符号恒等式。

## 原短输入与本次结果

下列各式分开以严格 release CLI 检查，不依赖前一输入保存的事实。

### sum-constant

```litex
have n N+
have c R
have f,g fn(k Z)R
sum(1,n,fn(k Z)R{c})=n*c
```

结果：`success=false`，exit `1`，`session_error=null`。首败 `search_proof`；没有解析或原目标 WD 失败。

### sum-add

```litex
have n N+
have c R
have f,g fn(k Z)R
sum(1,n,fn(k Z)R{f(k)+g(k)})=sum(1,n,f)+sum(1,n,g)
```

结果：`success=true`，exit `0`，`session_error=null`。

### sum-sub

```litex
have n N+
have c R
have f,g fn(k Z)R
sum(1,n,fn(k Z)R{f(k)-g(k)})=sum(1,n,f)-sum(1,n,g)
```

结果：`success=true`，exit `0`，`session_error=null`。

### sum-scale

```litex
have n N+
have c R
have f,g fn(k Z)R
sum(1,n,fn(k Z)R{c*f(k)})=c*sum(1,n,f)
```

结果：`success=true`，exit `0`，`session_error=null`。

### sum-pointwise

```litex
have n N+
have c R
have f,g fn(k Z)R
sum(1,n,fn(k Z)Z{k+k})=sum(1,n,fn(j Z)Z{2*j})
```

结果：`success=false`，exit `1`，`session_error=null`。首败 `search_proof`；没有解析或原目标 WD 失败。

### product-constant

```litex
have n N+
have c R*
product(1,n,fn(k Z)R*{c})=c^n
```

结果：`success=false`，exit `1`，`session_error=null`。首败 `search_proof`；没有解析或原目标 WD 失败。

### finite-sum-add

```litex
have S finite_set
have c R
have f,g fn(k S)R
finite_set_sum(S,fn(k S)R{f(k)+g(k)})=finite_set_sum(S,f)+finite_set_sum(S,g)
```

结果：`success=true`，exit `0`，`session_error=null`。

### finite-sum-sub

```litex
have S finite_set
have c R
have f,g fn(k S)R
finite_set_sum(S,fn(k S)R{f(k)-g(k)})=finite_set_sum(S,f)-finite_set_sum(S,g)
```

结果：`success=true`，exit `0`，`session_error=null`。

### finite-sum-scale

```litex
have S finite_set
have c R
have f,g fn(k S)R
finite_set_sum(S,fn(k S)R{c*f(k)})=c*finite_set_sum(S,f)
```

结果：`success=true`，exit `0`，`session_error=null`。

### finite-product-distribute

```litex
have S finite_set
have c R
have f,g fn(k S)R
finite_set_product(S,fn(k S)R{f(k)*g(k)})=finite_set_product(S,f)*finite_set_product(S,g)
```

结果：`success=true`，exit `0`，`session_error=null`。

## 已有完整证明与解释边界

- [sum.lit](../../sum.lit)：16 个顶层语句全部通过。常量项用归纳；点态替换先 `by fn_extension` 证明两个函数相等，再由求和读取函数等式。加减与常数倍的原显式归纳也通过。
- [product.lit](../../product.lit)：11 个顶层语句全部通过。保留非零实数 c 和正整数 n，归纳步展开最后一项，再合并整数幂。
- [sum_of_finite_set.lit](../../sum_of_finite_set.lit)：13 个顶层语句全部通过。
- [product_of_finite_set.lit](../../product_of_finite_set.lit)：12 个顶层语句全部通过。
- [aggregate_identities.lit](../../../proof_nodes/equal/by_builtin_rule/aggregate_identities.lit)：28 个顶层语句全部通过。

当前源码已有常量、加减、标量及点态乘法的 AggregateIdentityBuiltinRuleProof 分支，不能把旧搜索失败说成缺少全部数学规则。旧有限集实值接口在受限逐点前提核验中存在返回载体向 C 的消费边界；原作者证明通过局部 C 定理、fn_set_member 与点态替换连接原 R 目标。本次原 R 短输入及四个 C 签名对照均通过。新源码另已有 known_fn_application_standard_superset 的标准返回集合包含读取；本轮没有做删除/回退因果对照，不把它断言为唯一原因。

剩余三个短输入的外部边界精确到 search_proof；未输出内部失败证书，不能猜定为缺类型、归一化或缺规则的单一根因。保留为可选短接口能力观察；它们已有同目标显式证明，不重新登记为数学能力缺失。

历史作者解法见 [Round7](../../../../plan/迁移的plan/experience/problem_notes/example_authoring_round7_2026-10-04.md)、[Round8](../../../../plan/迁移的plan/experience/problem_notes/example_authoring_round8_2026-10-04.md)、[Round10](../../../../plan/迁移的plan/experience/problem_notes/example_authoring_round10_2026-10-04.md)、[Round11](../../../../plan/迁移的plan/experience/problem_notes/example_authoring_round11_2026-10-04.md)。

## 记录维护与证据

按照用户“完成后从具体纠错记录删掉”的要求，R04/R05/R06 的旧失败段落移出活动记录。总计划只保留原编号的关闭链接；原始失败、当前短接口边界和原作者证明全部保留为历史/经验。没有修改其他问题的完成状态。

[机器记录](../../proof_journals/symbolic_aggregate_status_2026-10-04.json)及[源码、程序、完整 CLI 输出归档](../../proof_journals/symbolic_aggregate_status_2026-10-04_receipts.zip)保存实际源码与二进制 SHA、输入、输出、首败、五个完整文件和共享目录漂移。本轮是 14 个独立短输入/载体对照及五个文件门；没有 Rust 测试、全 Obj 或发布门证书。
