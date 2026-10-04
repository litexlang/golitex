# eval 核验并存储结果等式 — 2026-10-04

用户明确更新了命令语义：成功的 `eval expr` 应存入 `expr = result`，供后续事实读取。Obj R03 / 总清单 OBJ02 按这个显式计算接口关闭；不扩大普通等式搜索的算法执行权限。

```litex
algo flag(x R) R by cases:
    case x=0:0
    case x!=0:1
eval sum(0,3,flag)
sum(0,3,flag)=3
sum(0,3,flag)+1=4
```

旧 release 显示 `3` 后拒绝第二行等式；新命令实际发布 `sum(0,3,flag)=3`，后续断言读取同一个 FactId。有限集原例 `eval finite_set_sum({1/3,2/3},flag)` 同样发布等于 `2` 的事实。区间及有限集 product、嵌套算法参数、递归算法、tuple 和精确根式也保留既有计算能力。

执行顺序是原表达式 WD、已存数值等式重写、有限精确计算、逐项算法定义方程核验、结果等式 WD、现有 `store_fact_and_infer`。计算链本身是证明证书；每个实际执行的算法调用额外保留定义方程的 VerifyFactResult。未改变 AST/Env/Runtime 字段、全局搜索等级、资源预算或 KB 表示。

正常 JSON 的 `stores` 列出真实等式；Detailed 保留 source/result、重写引用、计算链、算法方程证明、等式 WD、FactId 和 store/infer 结果。所有十种输出语言均验收。失败依赖现有 exec_stmt 事务回滚；局部 sketch 中的等式不泄漏，失败后会话还能读取此前已提交的等式。新能力不使用 trust。

可运行 tracer：[eval_store_result.lit](../../../stmt_nodes/command/eval_store_result.lit)。原例与最近反例、会话块及完整输出见[机器验收](../../proof_journals/eval_store_result_2026-10-04.json)和[源码/程序/回执](../../proof_journals/eval_store_result_2026-10-04_receipts.zip)。

## 定向验收

- release 构建通过；冻结源码的 16 个 eval、9 个语句边界、3 个函数 WD、63 个 JSON Rust 测试通过。
- 较宽事务组 134/137 通过；集合非成员、符号分式、模板递归三个失败与原审计记录相同，输入没有 eval。这些仍归原拥有者，不报告该组全绿。
- EvalStmt、DefAlgoByCasesStmt、DefAlgoByInducStmt collector 共 25/25；10 个 strict CLI 文件/配对输入、11 个相关文档代码块符合预期；持久会话 10/10 块符合预期。
- 错误 sum/有限和、除零、负根、算法参数域和 1024 项预算边界仍拒绝。Rust 额外核验 actual FactId、失败 claim 回滚与成功 sketch 不外泄。
- 共享工作区 release 同样构建成功，production 源码与冻结副本一致，二进制 SHA 相同；主 tracer、wrong-sum 和除零再次符合预期。现有 sum、product、sum_of_finite_set、product_of_finite_set 四个 Obj 整文件及 source-domain tracer 通过。
- 两个 sqrt 测试的旧表示期望迁移到既有精确结果：0.36 的平方根为 3/5，sqrt(2) 保持精确根式。这不是新增近似算法。

冻结源与二进制身份以机器记录为准；共享目录的其他修改单列。未运行全 Obj、全仓发布、教材或 Lean 门，不把局部验收当全仓证明。

## 清单维护

已验收的问题从活动纠错段落删除，解法保存在 experience，原始输出与代码留在 journal/receipt。总计划保留原编号的一行关闭记录及链接，不重排其余问题。R01、R03 按本规则移除；R02 的误诊已撤回，也移出活动清单。旧短自动化路线、冻结门禁统计和原始回执保留为历史，不能重开已选作者路线或覆盖后续证据。
