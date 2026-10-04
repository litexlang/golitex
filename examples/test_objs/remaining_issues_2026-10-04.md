# Obj 活动纠错记录 — 原审计 2026-10-04

> **统一收尾入口：** [src收尾总清单.md](../../plan/src收尾总清单.md)（2026-10-04）。活动事项及跨来源去重在总清单维护；本页保留专项代码、决定和历史验收。新增进展应同步对应总清单ID，不能用旧快照覆盖新证据。

## 活动项维护

解决一项并完成验收后，删除它的具体纠错段落；总计划只留原编号的关闭状态及解法链接，原始代码/输出归档不改。R01 的[显式反证链](experience/problem_notes/imaginary_contra_explicit_chain_2026-10-04.md)和 R03 的[eval 结果发布](experience/problem_notes/eval_store_result_2026-10-04.md)已移除；R02 的误诊撤回见下方纠正。其余原编号不重排。

R04/R05/R06 的[本次复核](experience/problem_notes/symbolic_aggregate_status_2026-10-04.md)确认显式作者目标已全部通过，原短输入已有 7/10 直接通过；三项旧失败段落也已移出活动记录。三个短搜索限制保留在经验中。

以下版本和统计属于原冻结审计，不是当前源码的门禁成绩。当前 `eval` 成功时核验并存储 `source = result`；旧 display-only 观察只作历史。

## 原审计任务与版本

- 用户任务：全部列出当前已观察到的问题，给出实际代码；原审计只记录，不修实现。
- 范围：全部 Obj 文件与负例、普通 Obj 独立正例、Stmt、基础合同、Rust 库与语句集成测试、67个旧原始输入、43个旧命名探针、44个现存公开文件、4个 showcase 前缀。
- 固定源码 SHA-256：`8cd780d5598c250eac50bb668bda31a1a68f23c63a4bb11f2dc484cc8f0039ba`。
- 新构建 release SHA-256：`d47a2b0ca55a0f8235810fdd57fde3a1fe74968cfa979172efdad7270a7a02ab`。
- 编译、测试与例子使用固定副本；保留真实模块配置，独立执行所得输出没有拼接到其他版本。
- 本轮之前曾出现E0603私有函数跨模块调用的中间构建失败；随后源码修复，最终固定版本构建成功。它保留在早期receipt中，不列为最终版本尚存编译错误。

[完整机器记录](proof_journals/remaining_issues_2026-10-04.json) · [源码、程序及完整输出归档](proof_journals/remaining_issues_2026-10-04_receipts.zip)

## 同日纠正

独立门禁复用了早期代码，八项主动代码与最终固定文件不同。按实际固定文件重新提取并重跑，**640/651通过、11拒绝**。R02“同样代码依赖整文件上下文”撤回：被比较的是旧短输入与新完整证明。其余门禁记录保留原版本身份。原始receipt保持不变。

[纠正说明](nonzero_union_correction_2026-10-04.md) · [新机器记录](proof_journals/nonzero_union_correction_2026-10-04.json) · [纠正receipt](proof_journals/nonzero_union_correction_2026-10-04_receipts.zip)。

## 核验结果

| 门禁 | 最终固定版本结果 |
| --- | --- |
| Obj 整文件 | 93/99通过，6失败；665是库存正例ID数 |
| 普通 Obj 独立正例 | 640/651通过，11拒绝（同日按实际固定文件重新提取纠正） |
| Obj 负例 | 309/309正确拒绝 |
| 两个需要真实模块上下文的Obj文件 | 整文件通过；14个正例未拆到缺上下文的-e运行 |
| Stmt | 377/377符合预期，含132个负例 |
| 基础合同 | 174/175通过，1失败 |
| Rust --lib | 734/760通过，26失败；其中6个是旧路线/表示/输出断言 |
| Rust Stmt 集成 | 1/1通过 |
| 旧67个原始直接输入 | 25直接通过，42拒绝；后者含4个缺模块上下文输入、1个C命名冲突，不是42个内核bug |
| 同源串行反证 | 20次：12通过、8拒绝 |

失败数量互相重叠，不能相加当独立bug数。manifest的0个登记gap也不代表所有正例通过。

## 本轮复核后的活动项

原R07–R16、A01–A06、S01–S03、T01–T04、W01–W02的具体旧纠错段落已移出。
完整解法、迁移/边界分类及原输出保留在[本轮闭环](experience/problem_notes/remaining_scan_solved_2026-10-04.md)
和机器archived_issues；后续showcase/教材尚未过的不同目标在[当前剩余报告](remaining_issues_current_2026-10-04.md)。

### T05：Point phantom参数的carrier身份待决定

```litex
struct Point<K nonempty_set,S nonempty_set>:
    value S
    tag N
forall t &Point<N,R>:
    t $in &Point<Z,R>
```

当前接受。K不参与字段，可能是同一个字段集合；若所有泛型参数采用名义身份，则应区分。
这项是DEC04合同选择，没有证明错误数值等式；不满足实际字段类型/错误value的控制仍拒绝。
对应旧wrong-carrier Rust expectation仍保留，不能静默换成expected=true。

[当前实际验证与原控制](proof_journals/remaining_issues_current_2026-10-04.json)。
