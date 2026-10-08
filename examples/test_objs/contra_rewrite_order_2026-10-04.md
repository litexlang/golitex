# 反证重写顺序导致的非确定性 — 2026-10-04

任务：回答同一证明为什么有时通过、有时拒绝。仅诊断；正式内核没有修改。先前静态怀疑现已由逐条日志与固定顺序干预确认。

实际输入：

```lit
by contra:
    ? i != 0
    i * i = -1
    impossible i * i != 0
```

最后需要在反证假设`i=0`下证明`i*i=0`。闭合数值等式索引里有两条重叠替换：反证假设提供`i -> 0`，正文提供`i*i -> -1`。来源都合法，但算法把无序HashMap的遍历顺序当成逐条破坏性替换顺序，并只检查最后一个残余目标。

实际成功日志对应：

```text
i*i  -- i -> 0 -->  0*0
0*0  -- i*i -> -1 -->  0*0   （已经没有匹配的 i*i）
残余 0*0 = 0：通过
```

实际失败日志对应：

```text
i*i  -- i*i -> -1 -->  -1
-1   -- i -> 0 -->  -1       （已经没有 i）
残余 -1 = 0：拒绝
```

Rust实现的相关部分：

```rust
for (key, entries) in env.facts.known_closed_numeric_equal.iter() {
    // append to a Vec in HashMap iteration order
}
for (from_ir, closed, fact_id) in &entries {
    let next_left = replace_obj_matching_ir(&rewritten_left, from_ir, &closed_obj);
    // rewrite the already rewritten object
    rewritten_left = next_left;
}
// verify one final residual; a miss returns None
```

这是算法对无序容器的顺序产生了依赖。Rust默认HashMap使用随机种子，遍历顺序没有保证；新进程的候选顺序能改变。见[Rust HashMap官方文档](https://doc.rust-lang.org/std/collections/struct.HashMap.html)。搜索结果不应随这个顺序改变。

## 因果验证

使用上轮固定源码构建的程序，保持原输入。正式源码未改；在临时源码副本的同一叶子中增加stderr日志，并允许诊断环境变量对局部候选Vec按FactId排序。

| 诊断模式 | 次数 | 结果 |
| --- | --- | --- |
| 原程序 | 20 | 9通过、11拒绝 |
| 加日志、保留原哈希遍历 | 30 | 16通过、14拒绝 |
| 强制先`i*i -> -1` | 20 | 20拒绝 |
| 强制先`i -> 0` | 20 | 20通过 |

全部70个带日志的原输入运行都一一对应：`i -> 0`先用的36次全部通过；`i*i -> -1`先用的34次全部拒绝。日志包含每条候选、来源FactId、替换前后表达式，以及残余验证结果，直接填补了上轮没有读取失败时顺序的证据缺口。

这里`i*i=-1`的FactId是f2，反证假设`i=0`是f4；oldest/newest只是诊断排序标签，FactId分配包括解析阶段，不能当成事实执行时间或一般修复原则。

三种诊断模式还分别核验了以下五个独立控制输入（15/15符合预期）：

```lit
# 通过
i != 0
3 + 4*i != 4 + 3*i

# 分别执行并拒绝的错误事实
# i = 0
# 3 + 4*i = 4 + 3*i
```

第五个输入是短反证，三种模式均通过：

```lit
by contra:
    ? i != 0
    impossible i != 0
```

## 用户决定：保留替换，显式写证明

用户在诊断后明确选择不改Rust，只把例子补为`i*i=0*0=0`。该证明已经在当前release 30/30独立新进程通过，并纳入Stmt例子和Obj P103。见作者修复记录 (historical task record; retired)。历史顺序诊断仍成立；原简写的自动证明边界保留，不再作为本例待实现的Rust修复任务。

## 历史修复讨论（未实施，用户已选择作者路线）

原因已确认，正式内核仍待修复。简单排序最多让结果固定，坏顺序会固定为20/20失败。修复需要解决重叠替换对可用路径的遮蔽，在现有权限/终止边界内保留并验证证明来源；不能用固定随机种子、增加i非零特例或无限扩大搜索来掩盖问题。

本轮没有提出或实施共享Env/Runtime/AST结构与状态合同变化。诊断环境变量和排序仅存在于已清理的临时副本及receipt，不是生产功能。

## 身份与重放

原固定源码：`36876aef82db464bf805f02abd38636c516ca6a892d31e328034698f3d558c9d`；base binary：`288b50777e68d743572dab25af99dab06444124e2680e8ece6370626c63334ef`。诊断只改副本中的单一重写叶子，差异完整保存。diagnostic source：`a2c78f0887668b3b70f44df42176cd3bce63da829df6ecccfaf76ee53cca6737`；binary：`f75f707eb86f218263126fb0af6ba20c9174bd410d0477bbe27e6565ab1841c7`。正式对应文件在任务开始/结束哈希相同。

机器记录 (historical task record; retired) · [完整receipt](proof_journals/contra_rewrite_order_2026-10-04_receipts.zip)（SHA-256 `e01f884c34101884e2114eace95cd7ad981c044ccc03fc890d12eb8030765d13`）。保存固定原/诊断程序、诊断源码、源文件差异、构建输出、全部stdout/stderr、输入、参数与解析脚本。原源码归档引用上轮receipt的`current-source.zip`；其receipt SHA-256：`dc0ae3371b3972e4b3c8f2380fd8e7bfdd57140b33537c311a6856c4d8acf94a`。

复现：从receipt取出`litex-diagnostic`，用原完整输入执行`-strict -lang en -e <代码>`；不设置诊断变量保留原遍历，`LITEX_DIAG_REWRITE_ORDER=oldest`强制坏顺序，`newest`强制好顺序。诊断变量只对该复制程序有效。正式CLI的success和exit均核验，日志不作为成功判据。
