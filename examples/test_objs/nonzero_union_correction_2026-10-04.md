# i 非零与 union 审计纠正 — 2026-10-04

任务：回答用户第1/2项，并纠正错误的审计比较。本次仅诊断和记录，没有修改内核或正式证明用例。

## 直接输入与现有规则

```lit
i != 0
3 + 4*i != 4 + 3*i
```

两条输入在原固定release和新release各20/20通过。已有`ImaginaryUnitNonzero`与`ClosedComplex` BT rule；实际先走`by_closed_calculation`。精确复数坐标为`(3,4)`与`(4,3)`，无需浮点近似。

以下等式通过：

```lit
3 + 4*i = 4*i + 3
3 - 4*i = -4*i + 3
```

以下是分别执行并拒绝的错误输入：

```lit
i = 0
i != i
3 + 4*i = 4 + 3*i
3 + 4*i != 4*i + 3
```

规则：`src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/search_atomic_except_equality_fact_proof_by_builtin_rules/not_equal.rs`。计算分支：`src/execute/execute_fact_stmt/verify_atomic_fact/calculate_closed_atomic_fact.rs`。

后续已用逐条日志与固定顺序干预确认R01原因，见[重写顺序诊断](contra_rewrite_order_2026-10-04.md)。下文“静态诊断/尚未逐次读取”的表述记录本页最初检查点；新证据已补齐，正式实现仍未修复。

## R01：反证收尾仍不稳定

实际原输入：

```lit
by contra:
    ? i != 0
    i * i = -1
    impossible i * i != 0
```

反证先假设`i=0`。`impossible i*i!=0`收尾须同时核验`i*i!=0`及其否定`i*i=0`。失败精确落在后一条：`by_contra -> closing -> negated_impossible -> equality search_proof: i*i=0`。直接`i!=0`能证明，不会自动替代作者指定的反证正文。

原归档首次20次12通过/8拒绝的记录保持；本次同归档程序20次13通过/7拒绝；新release20次6通过/14拒绝。都是同一不可变程序的串行新进程。相同新源码重新构建的详细诊断30次17通过/13拒绝；详细投影仅用于查看证明，不把它混入CLI门禁计数。

详细成功证明实际使用：

```lit
# 在反证假设 i=0 的局部环境中：
i*i = 0*0 = 0
```

Rust成功证书为`ClosedNumericEqualSubstitution`，`rewritten_left="0 * 0"`、`rewritten_right="0"`，引用反证假设的FactId。源码同时将`i=0`与正文`i*i=-1`加入闭合数值替换索引；索引按`HashMap`遍历并逐条替换重叠子树：

```rust
for (key, entries) in env.facts.known_closed_numeric_equal.iter() {
    // collect entries in iteration order
}
for (from_ir, closed, fact_id) in &entries {
    let next_left = replace_obj_matching_ir(&rewritten_left, from_ir, &closed_obj);
    // continue rewriting the already rewritten object
}
```

静态诊断：先替换`i -> 0`会得到`0*0=0`；先替换`i*i -> -1`会得到`-1=0`，而只选一次重写会错过另一条路径。成功证书已确认第一条路径，失败输出只保留搜索未找到证明，没有保存尝试过的重写，故不声称已逐次读取失败时的索引顺序。本次未修此顺序问题。

已有两个已验证的证明对照。短反证在两版本各20/20通过：

```lit
by contra:
    ? i != 0
    impossible i != 0
```

显式同余链保留原`impossible`尾部，在两版本各10/10通过：

```lit
by contra:
    ? i != 0
    i * i = i * 0
    i * 0 = 0
    i * i = 0
    i * i = -1
    impossible i * i != 0
```

它们证明故障边界，不表示原非确定性已经修复。

## R02撤回：被比较的是不同代码

旧短输入拒绝于未能证明`union({1},{2}) $subset {1,2}`：

```lit
sketch:
    by extension union({1}, {2}) = {1, 2}
```

实际固定文件P01已改成完整的两方向成员证明与分情况：

```lit
sketch:
    by extension:
        ? union({1}, {2}) = {1, 2}
        claim:
            ? forall x union({1}, {2}):
                x $in {1, 2}
            x $in {1} or x $in {2}
            by cases:
                ? x $in {1, 2}
                case x $in {1}:
                    x = 1
                    x $in {1, 2}
                case x $in {2}:
                    x = 2
                    x $in {1, 2}
        claim:
            ? forall x {1, 2}:
                x $in union({1}, {2})
            x = 1 or x = 2
            by cases:
                ? x $in union({1}, {2})
                case x = 1:
                    x $in union({1}, {2})
                case x = 2:
                    x $in union({1}, {2})
```

完整P01在纠正651项门禁中独立通过，在归档与新release又各独立3/3通过；两版本整文件也通过。旧短输入没有这些证明步骤，不能据此宣称同样代码依赖整文件上下文。R02撤回并致歉。

## 八项输入与统计纠正

原`frozen_audit.py`复用了早期独立输入，未从最终固定文件重新提取。主动代码不同的八项在实际当前固定文件中已展开证明，均独立通过：

- `union-P01`
- `union-P05`
- `intersect-P05`
- `set_minus-P06`
- `set_builder-P06`
- `anonymous_fn-P06`
- `sum-P106`
- `instantiated_template_obj-P04`

另有`index_cart-P05`只删除尾部注释，前后都通过。全部651项已按实际归档文件重新提取运行，**640通过、11拒绝**；另14项需要真实模块上下文，仍保留实际拥有者门禁。93/99 Obj整文件、309负例及Stmt/基础/Rust原门禁的版本与输出不变。剩余11项：

- `fn_set-P04`
- `sum-P107`
- `sum-P108`
- `product-P103`
- `sum_of_finite_set-P103`
- `sum_of_finite_set-P106`
- `product_of_finite_set-P103`
- `finite_set_reduce-P02`
- `finite_set_reduce-P03`
- `finite_set_reduce-P04`
- `finite_set_reduce-P05`

## 身份与复现

原固定源码：`8cd780d5598c250eac50bb668bda31a1a68f23c63a4bb11f2dc484cc8f0039ba`；binary：`d47a2b0ca55a0f8235810fdd57fde3a1fe74968cfa979172efdad7270a7a02ab`。

新聚焦源码：`36876aef82db464bf805f02abd38636c516ca6a892d31e328034698f3d558c9d`；release binary：`288b50777e68d743572dab25af99dab06444124e2680e8ece6370626c63334ef`。新构建前后与源码归档身份稳定；之后共享工作区继续变化，后续变化不在本门禁内。651项纠正仍使用原固定版本，没有混入新版本。详细诊断由相同新源码归档独立构建，经`Runtime::run_litex_code -> exec_stmt`执行，证明投影不修改内核。

[机器记录](proof_journals/nonzero_union_correction_2026-10-04.json) · [新receipt](proof_journals/nonzero_union_correction_2026-10-04_receipts.zip)（SHA-256 `dc0ae3371b3972e4b3c8f2380fd8e7bfdd57140b33537c311a6856c4d8acf94a`）。原receipt保持不变（SHA-256 `c8ba2fdb40b4dc22eeb30dd16c05026e88e33f85d96498d0185b1868ad14880e`）。新receipt保存651项实际代码/完整输出、聚焦输入/输出、新源码/程序、详细诊断与复现脚本。原固定源码/程序引用原receipt的`verified/source-frozen.zip`和`verified/litex-frozen`。

复现使用新receipt内`correct_archived_gate.py`与`focused_probes.py`。当前CLI命令`litex -strict -lang en -e <完整代码>`，整文件`litex -strict -lang en -f <union.lit>`；成功同时要求JSON `success=true`且exit0，错误输入同时要求`success=false`且exit1。
