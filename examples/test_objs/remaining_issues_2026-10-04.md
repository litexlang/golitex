# 尚存问题完整审计 — 2026-10-04

> **统一收尾入口：** [src收尾总清单.md](../../plan/src收尾总清单.md)（2026-10-04）。活动事项及跨来源去重在总清单维护；本页保留专项代码、决定和历史验收。新增进展应同步对应总清单ID，不能用旧快照覆盖新证据。

## 任务与版本

- 用户任务：全部列出当前已观察到的问题，给出实际代码；本轮不修实现。
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

## 逐项问题

### R01：已按用户选择改为显式等式链（仅Litex作者修复）

**最新处理决定**：用户明确选择保留现有替换，不改Rust。当前可运行例子已补上下面等式链，保留原目标和收尾，30/30独立新进程通过，Stmt与Obj拥有者文件通过：

```lit
by contra:
    ? i != 0
    i * i = -1
    i * i = 0 * 0 = 0
    impossible i * i != 0
```

[解决记录](experience/problem_notes/imaginary_contra_explicit_chain_2026-10-04.md) · [当前Stmt例子](../stmt_nodes/by/by_contra_imaginary_unit.lit) · [Obj P103](imaginary_unit.lit)。本项作为例子任务已解决；下文是未补桥的旧简写行为与历史诊断，Rust自动替换并未改变，不再为本项安排Rust修复。


- 分类：重叠等式替换的顺序依赖已确认；主标签：`kernel_problem`；最早边界：explicit proof / by_contra / builtin rewrite。
- 观察：串行20次：12通过、8拒绝；同时直接 i!=0 通过。
- 本项处理：用户选择补显式乘法替换链；当前例子已验收。旧自动简写保留为已知边界，不安排Rust修复。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：contra-serial**

```lit
by contra:
    ? i != 0
    i * i = -1
    impossible i * i != 0
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "by contradiction", "why_failed": {"type": "by", "rule_name": "By contradiction", "message": "Prove by contradiction", "phase": "by_contra", "failure": {"phase": "closing", "failure": {"phase": "negated_impossible", "result": {"type": "equality", "success": false, "phase": "search_proof", "fact": "i * i = 0", "well_defined": {"left": {"type": "by_known", "obj": "i * i", "wd_id": "wd3"}, "right": {"type": "by_known", "obj": "0", "wd_id": "wd2"}}}}}}, "stores": [], "infers": []}`。

对照：old-i-nonzero: 通过。

执行类别：已验收Litex作者修复，保持原数学目标，无trust，负例仍拒绝；历史Rust机制未改。

**同日澄清**：源码已有`ImaginaryUnitNonzero`与`ClosedComplex` BT rule。以下直接输入在归档和新release各20/20通过，实际先命中精确`by_closed_calculation`：

```lit
i != 0
3 + 4*i != 4 + 3*i
```

原反证在新release仍不稳定（20次6通过、14拒绝），失败是收尾`negated_impossible`对`i*i=0`的搜索，不是缺`i!=0`规则。详细成功证明将`i*i`重写为`0*0`。源码显示`HashMap`遍历中的父/子重叠替换存在顺序依赖；具体证据与已通过的对照证明见[纠正说明](nonzero_union_correction_2026-10-04.md)。本次未修实现。

**后续因果确认**：[重写顺序诊断](contra_rewrite_order_2026-10-04.md)已保存失败时的实际遍历及残余目标。70次带日志运行全部吻合，40次固定顺序干预确定改变结果。原归档与新诊断版本分别记录；没有实现修复。

### R02：撤回——两份不同证明被误作同一输入

分类：审计错误；不是已确认的上下文内核问题。原短写法：

```lit
sketch:
    by extension union({1}, {2}) = {1, 2}
```

实际固定文件的P01已展开两方向成员证明与分情况，独立执行通过，整文件通过。旧短写法没有这些证明步骤，它的拒绝不能证明完整代码依赖外部上下文。完整前后代码和八项对照见[纠正说明](nonzero_union_correction_2026-10-04.md)。旧输入/结果仍保存为历史直接自动化边界证据。

### R03：algo 聚合能 eval，等式证明失败

- 分类：行为问题，根因暂定；主标签：`kernel_problem`；最早边界：proof search。
- 观察：sum 和 finite_set_sum 的等式拒绝；相同表达式 eval 分别返回3和2；flag(1)=1通过。
- 下一步：检查 checked algo 调用方程如何进入 aggregate 的等式验证，核对计算证据和 WD 证据。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：flag-sum**

```lit
algo flag(x R) R by cases:
    case x=0:0
    case x!=0:1
sum(0,3,flag)=3
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "sum(0, 3, flag) = 3", "why_failed": {"phase": "search_proof", "goal": "sum(0, 3, flag) = 3"}, "stores": [], "infers": []}`。

**实际输入：flag-finite-sum**

```lit
algo flag(x R) R by cases:
    case x=0:0
    case x!=0:1
finite_set_sum({1/3,2/3},flag)=2
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "finite_set_sum({1 / 3, 2 / 3}, flag) = 2", "why_failed": {"phase": "search_proof", "goal": "finite_set_sum({1 / 3, 2 / 3}, flag) = 2"}, "stores": [], "infers": []}`。

对照：flag-call: 通过；flag-sum-eval: 通过，eval=3；flag-finite-sum-eval: 通过，eval=2。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### R04：符号 sum 的常量、线性、同点值替换不通过

- 分类：行为问题，根因暂定；主标签：`kernel_problem`；最早边界：proof search。
- 观察：五条独立输入全部拒绝；分段求和通过，不能将整个 sum 能力判为缺失。
- 下一步：分别检查常量项数、函数载体、点态证据和 sum 规则入口。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：sum-constant**

```lit
have n N+
have c R
have f,g fn(k Z)R
sum(1,n,fn(k Z)R{c})=n*c
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "sum(1, n, fn (k Z) R{c}) = n * c", "why_failed": {"phase": "search_proof", "goal": "sum(1, n, fn (k Z) R{c}) = n * c"}, "stores": [], "infers": []}`。

**实际输入：sum-add**

```lit
have n N+
have c R
have f,g fn(k Z)R
sum(1,n,fn(k Z)R{f(k)+g(k)})=sum(1,n,f)+sum(1,n,g)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "sum(1, n, fn (k Z) R{f(k) + g(k)}) = sum(1, n, f) + sum(1, n, g)", "why_failed": {"phase": "search_proof", "goal": "sum(1, n, fn (k Z) R{f(k) + g(k)}) = sum(1, n, f) + sum(1, n, g)"}, "stores": [], "infers": []}`。

**实际输入：sum-sub**

```lit
have n N+
have c R
have f,g fn(k Z)R
sum(1,n,fn(k Z)R{f(k)-g(k)})=sum(1,n,f)-sum(1,n,g)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "sum(1, n, fn (k Z) R{f(k) - g(k)}) = sum(1, n, f) - sum(1, n, g)", "why_failed": {"phase": "search_proof", "goal": "sum(1, n, fn (k Z) R{f(k) - g(k)}) = sum(1, n, f) - sum(1, n, g)"}, "stores": [], "infers": []}`。

**实际输入：sum-scale**

```lit
have n N+
have c R
have f,g fn(k Z)R
sum(1,n,fn(k Z)R{c*f(k)})=c*sum(1,n,f)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "sum(1, n, fn (k Z) R{c * f(k)}) = c * sum(1, n, f)", "why_failed": {"phase": "search_proof", "goal": "sum(1, n, fn (k Z) R{c * f(k)}) = c * sum(1, n, f)"}, "stores": [], "infers": []}`。

**实际输入：sum-pointwise**

```lit
have n N+
have c R
have f,g fn(k Z)R
sum(1,n,fn(k Z)Z{k+k})=sum(1,n,fn(j Z)Z{2*j})
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "sum(1, n, fn (k Z) Z{k + k}) = sum(1, n, fn (j Z) Z{2 * j})", "why_failed": {"phase": "search_proof", "goal": "sum(1, n, fn (k Z) Z{k + k}) = sum(1, n, fn (j Z) Z{2 * j})"}, "stores": [], "infers": []}`。

对照：sum-split: 通过。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### R05：符号 product 常量幂不通过

- 分类：行为问题，根因暂定；主标签：`kernel_problem`；最早边界：proof search。
- 观察：product(1,n,常量c)=c^n拒绝，符号分段乘积通过。
- 下一步：检查正整数项数与常量函数匹配，不扩大通用搜索。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：product-constant**

```lit
have n N+
have c R*
product(1,n,fn(k Z)R*{c})=c^n
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "product(1, n, fn (k Z) R*{c}) = c ^ n", "why_failed": {"phase": "search_proof", "goal": "product(1, n, fn (k Z) R*{c}) = c ^ n"}, "stores": [], "infers": []}`。

对照：product-split: 通过。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### R06：有限集求和线性与乘积乘法分配不通过

- 分类：行为问题，根因暂定；主标签：`kernel_problem`；最早边界：proof search。
- 观察：有限集常量求和和常量乘积通过；加、减、缩放和乘积点态乘法公式分别拒绝。
- 下一步：检查有限集 carrier、lambda 展开与规则保留的点态证书。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：finite-sum-add**

```lit
have S finite_set
have c R
have f,g fn(k S)R
finite_set_sum(S,fn(k S)R{f(k)+g(k)})=finite_set_sum(S,f)+finite_set_sum(S,g)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "finite_set_sum(S, fn (k S) R{f(k) + g(k)}) = finite_set_sum(S, f) + finite_set_sum(S, g)", "why_failed": {"phase": "search_proof", "goal": "finite_set_sum(S, fn (k S) R{f(k) + g(k)}) = finite_set_sum(S, f) + finite_set_sum(S, g)"}, "stores": [], "infers": []}`。

**实际输入：finite-sum-sub**

```lit
have S finite_set
have c R
have f,g fn(k S)R
finite_set_sum(S,fn(k S)R{f(k)-g(k)})=finite_set_sum(S,f)-finite_set_sum(S,g)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "finite_set_sum(S, fn (k S) R{f(k) - g(k)}) = finite_set_sum(S, f) - finite_set_sum(S, g)", "why_failed": {"phase": "search_proof", "goal": "finite_set_sum(S, fn (k S) R{f(k) - g(k)}) = finite_set_sum(S, f) - finite_set_sum(S, g)"}, "stores": [], "infers": []}`。

**实际输入：finite-sum-scale**

```lit
have S finite_set
have c R
have f,g fn(k S)R
finite_set_sum(S,fn(k S)R{c*f(k)})=c*finite_set_sum(S,f)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "finite_set_sum(S, fn (k S) R{c * f(k)}) = c * finite_set_sum(S, f)", "why_failed": {"phase": "search_proof", "goal": "finite_set_sum(S, fn (k S) R{c * f(k)}) = c * finite_set_sum(S, f)"}, "stores": [], "infers": []}`。

**实际输入：finite-product-distribute**

```lit
have S finite_set
have c R
have f,g fn(k S)R
finite_set_product(S,fn(k S)R{f(k)*g(k)})=finite_set_product(S,f)*finite_set_product(S,g)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "finite_set_product(S, fn (k S) R{f(k) * g(k)}) = finite_set_product(S, f) * finite_set_product(S, g)", "why_failed": {"phase": "search_proof", "goal": "finite_set_product(S, fn (k S) R{f(k) * g(k)}) = finite_set_product(S, f) * finite_set_product(S, g)"}, "stores": [], "infers": []}`。

对照：finite-sum-constant: 通过；finite-product-constant: 通过。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### R07：非空 finite_set_reduce 计算与等式验证不一致

- 分类：行为问题，根因暂定；主标签：`kernel_problem`；最早边界：proof search。
- 观察：单元素、多元素、重排序、初始值10的加法 fold 等式均拒绝；非空 eval 返回6，空集等式通过。
- 下一步：先检查合法 AC fold 的展开方程到等式验证的路径；保留非交换减法/非法域负例。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：finite_set_reduce-P02**

```lit
sketch:
    finite_set_reduce({2}, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 0) = 2
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "sketch", "why_failed": {"type": "proof_block", "rule_name": "Sketch", "message": "Run a sketch proof block", "phase": "sketch", "failure": {"step_index": 0, "result": {"success": false, "statement": "finite_set_reduce({2}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 0) = 2", "why_failed": {"phase": "search_proof", "goal": "finite_set_reduce({2}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 0) = 2"}, "stores": [], "infers": []}}}, "stores": [], "infers": []}`。

**实际输入：finite_set_reduce-P03**

```lit
sketch:
    finite_set_reduce({1, 2}, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 0) = 3
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "sketch", "why_failed": {"type": "proof_block", "rule_name": "Sketch", "message": "Run a sketch proof block", "phase": "sketch", "failure": {"step_index": 0, "result": {"success": false, "statement": "finite_set_reduce({1, 2}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 0) = 3", "why_failed": {"phase": "search_proof", "goal": "finite_set_reduce({1, 2}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 0) = 3"}, "stores": [], "infers": []}}}, "stores": [], "infers": []}`。

**实际输入：finite_set_reduce-P04**

```lit
sketch:
    finite_set_reduce({2, 1}, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 0) = 3
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "sketch", "why_failed": {"type": "proof_block", "rule_name": "Sketch", "message": "Run a sketch proof block", "phase": "sketch", "failure": {"step_index": 0, "result": {"success": false, "statement": "finite_set_reduce({2, 1}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 0) = 3", "why_failed": {"phase": "search_proof", "goal": "finite_set_reduce({2, 1}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 0) = 3"}, "stores": [], "infers": []}}}, "stores": [], "infers": []}`。

**实际输入：finite_set_reduce-P05**

```lit
sketch:
    finite_set_reduce({1, 2}, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 10) = 13
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "sketch", "why_failed": {"type": "proof_block", "rule_name": "Sketch", "message": "Run a sketch proof block", "phase": "sketch", "failure": {"step_index": 0, "result": {"success": false, "statement": "finite_set_reduce({1, 2}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 10) = 13", "why_failed": {"phase": "search_proof", "goal": "finite_set_reduce({1, 2}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 10) = 13"}, "stores": [], "infers": []}}}, "stores": [], "infers": []}`。

对照：finite-reduce-eval: 通过，eval=6；finite-reduce-empty: 通过。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### R08：reduce 符号分段与有限乘积新增元素公式不通过

- 分类：行为问题，根因暂定；主标签：`kernel_problem`；最早边界：proof search。
- 观察：整数文字边界的 reduce 分段通过，forall 符号边界和 fresh insertion 不通过。
- 下一步：分开核对符号边界条件、函数域与新增元素条件，分别找最早失败。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：reduce-symbolic-split**

```lit
forall a,b,c Z,s R,f fn(k Z)R,op fn(x,y R)R:
    a<=b
    b<c
    =>:
        reduce(a,c,f,op,s)=reduce(b+1,c,f,op,reduce(a,b,f,op,s))
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "forall a, b, c Z, s R, f fn (k Z) R, op fn (x, y R) R:\n    a <= b\n    b < c\n    =>:\n        reduce(a, c, f, op, s) = reduce(b + 1, c, f, op, reduce(a, b, f, op, s))", "why_failed": {"phase": "search_proof", "goal": "forall a, b, c Z, s R, f fn (k Z) R, op fn (x, y R) R:\n    a <= b\n    b < c\n    =>:\n        reduce(a, c, f, op, s) = reduce(b + 1, c, f, op, reduce(a, b, f, op, s))"}, "stores": [], "infers": []}`。

**实际输入：finite-product-insert**

```lit
forall S finite_set,a R,f fn(x union(S,{a}))R:
    not a $in S
    =>:
        finite_set_product(union(S,{a}),f)=finite_set_product(S,fn(x S)R{f(x)})*f(a)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "forall S finite_set, a R, f fn (x union(S, {a})) R:\n    not a $in S\n    =>:\n        finite_set_product(union(S, {a}), f) = finite_set_product(S, fn (x S) R{f(x)}) * f(a)", "why_failed": {"phase": "search_proof", "goal": "forall S finite_set, a R, f fn (x union(S, {a})) R:\n    not a $in S\n    =>:\n        finite_set_product(union(S, {a}), f) = finite_set_product(S, fn (x S) R{f(x)}) * f(a)"}, "stores": [], "infers": []}`。

对照：reduce-literal-split: 通过。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### R09：递归短断言及模板递归仍缺自动展开

- 分类：直接自动搜索能力边界；Rust旧期望仍失败；主标签：`trust`；最早边界：proof search。
- 观察：两种 f(1)=0 短断言各10/10拒绝；显式递归等式链10/10通过，Stmt集成检查通过。
- 下一步：保留现有显式链。先核对短断言的既有自动化合同，再决定局部展开支持；不把用户已接受的 f(2) 显式链边界重新归为 bug。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：recursive-count**

```lit
have fn f(n N)N by induc n from 0:
    case n=0:0
    case n>=1:f(n-1)
f(0)=0
f(1)=0
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "f(1) = 0", "why_failed": {"phase": "search_proof", "goal": "f(1) = 0"}, "stores": [], "infers": []}`。

**实际输入：template-recursive**

```lit
template<_S set>:
    have fn f(n N)N by induc n from 0:
        case n=0:0
        case n>=1:f(n-1)
\f<{0}>(0)=0
\f<{0}>(1)=0
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "\\f<{0}>(1) = 0", "why_failed": {"phase": "search_proof", "goal": "\\f<{0}>(1) = 0"}, "stores": [], "infers": []}`。

对照：explicit-recursive-chain: 通过。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### R10：归纳步缺 n+1 的自然数载体证据

- 分类：行为问题，根因暂定；主标签：`kernel_problem`；最早边界：well_defined / induction step。
- 观察：普通和强归纳目标 f(n)=f(n)，在归纳步 f(n+1) 的 WD 要求 n+1 in N 时失败。正自然数前驱单独通过。
- 下一步：检查归纳域证据与 successor closure 的组合及所在 VerifyState。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：domain-induc**

```lit
have fn f(x N)N=x
by induc n from 0:
    ? f(n)=f(n)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "by induc", "why_failed": {"type": "by", "rule_name": "By induction", "message": "Prove by induction", "phase": "by_induc", "failure": {"phase": "step", "failure": {"phase": "goal", "goal_index": 0, "result": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "FnObj", "failure": {"phase": "requirement", "obj": "f(n + 1)", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "n + 1 $in N", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "ArithmeticOperator", "kind": "Add", "obj": "n + 1", "child_obj_well_defined": [{"type": "by_def", "family": "Identifier", "kind": "Identifier", "obj": "n"}, {"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact"…`。

**实际输入：domain-strong_induc**

```lit
have fn f(x N)N=x
by strong_induc n from 0:
    ? f(n)=f(n)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "by strong_induc", "why_failed": {"type": "by", "rule_name": "By strong induction", "message": "Prove by strong induction", "phase": "by_strong_induc", "failure": {"phase": "step", "failure": {"phase": "goal", "goal_index": 0, "result": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "FnObj", "failure": {"phase": "requirement", "obj": "f(n + 1)", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "n + 1 $in N", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "ArithmeticOperator", "kind": "Add", "obj": "n + 1", "child_obj_well_defined": [{"type": "by_def", "family": "Identifier", "kind": "Identifier", "obj": "n"}, {"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}], "requirement_fact_verified": [{"type": "atomic_except_equali…`。

**实际输入：induction-domain-file**

```lit
# Before: f(n) failed goal WD because n >= 0 was absent; have/by-def bodies
# were rejected as NonFactStmt even when their own statements were valid.
# have fn f(x N) N = x
# by induc n from 0:
#     ? f(n) = f(n)
# Now: goal WD uses n in Z and n >= from, without the induction hypothesis.
# Both proof cases use the ordinary checked proof-body executor.
# Boundary: from -1 for f : N -> N and ill-typed proof statements reject.
# Evidence: target/release/litex -strict -f examples/stmt_nodes/by/induction_domain_and_proof_actions.lit

have fn f(x N) N = x
by induc n from 0:
    ? f(n) = f(n)
    have a N = 0
    let b = a

prop same(x Z):
    x = x
by induc m from 0:
    ? $same(m)
    ? from m = 0:
        by def $same(0)
    ? induc:
        by def $same(m + 1)
# Recursive goals can now reach the case proofs. Prove the argument equality
# explicitly before using the recursive equation and induction hypothesis.
have fn countdown(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: countdown(n - 1)
by induc k from 0:
    ? countdown(k) = 0
    ? from k = 0:
        countdown(k) = 0
    ? induc:
        (k + 1) - 1 = k
        countdown(k + 1) = countdown((k + 1) - 1)
        countdown((k + 1) - 1) = countdown(k)
        countdown(k) = 0
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "by induc", "why_failed": {"type": "by", "rule_name": "By induction", "message": "Prove by induction", "phase": "by_induc", "failure": {"phase": "step", "failure": {"phase": "goal", "goal_index": 0, "result": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "FnObj", "failure": {"phase": "requirement", "obj": "f(n + 1)", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "n + 1 $in N", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "ArithmeticOperator", "kind": "Add", "obj": "n + 1", "child_obj_well_defined": [{"type": "by_def", "family": "Identifier", "kind": "Identifier", "obj": "n"}, {"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact"…`。

对照：predecessor-only: 通过；positive-predecessor-file: 通过。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### R11：有限性及基数规则组合失败

- 分类：行为问题，根因暂定；主标签：`kernel_problem`；最早边界：WD / proof composition。
- 观察：两层包含推出有限性失败；A仅声明set时的基数不等式失败；union({1},{2})的有限性在基数WD中未证出。直接有限子集和双方已声明finite_set的比较通过。
- 下一步：分别检查传递包含、派生有限性的消费和 union 的有限性证据。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：subset-finite-transitive**

```lit
forall A,B set,F finite_set:
    A $subset B
    B $subset F
    =>:
        $is_finite_set(A)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "forall A, B set, F finite_set:\n    A $subset B\n    B $subset F\n    =>:\n        $is_finite_set(A)", "why_failed": {"phase": "search_proof", "goal": "forall A, B set, F finite_set:\n    A $subset B\n    B $subset F\n    =>:\n        $is_finite_set(A)"}, "stores": [], "infers": []}`。

**实际输入：subset-cardinality**

```lit
forall A set,B finite_set:
    A $subset B
    =>:
        finite_set_size(A)<=finite_set_size(B)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "forall A set, B finite_set:\n    A $subset B\n    =>:\n        finite_set_size(A) <= finite_set_size(B)", "why_failed": {"phase": "search_proof", "goal": "forall A set, B finite_set:\n    A $subset B\n    =>:\n        finite_set_size(A) <= finite_set_size(B)"}, "stores": [], "infers": []}`。

**实际输入：union-cardinality**

```lit
finite_set_size(union({1},{2}))<=finite_set_size({1})+finite_set_size({2})
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "atomic_except_equality", "success": false, "phase": "well_defined", "failure": {"phase": "predicate_domain", "completed_requirements": [], "requirement": "finite_set_size(union({1}, {2})) $in R", "verify": {"type": "atomic_except_equality", "success": false, "phase": "well_defined", "failure": {"phase": "FiniteSetStat", "failure": {"phase": "FiniteSetSize", "failure": {"phase": "requirement", "obj": "finite_set_size(union({1}, {2}))", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "$is_finite_set(union({1}, {2}))", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetOperator", "kind": "Union", "obj": "union({1}, {2})", "child_obj_well_defined": [{"type": "by_def", "family": "SetFormer", "kind": "…`。

对照：subset-finite: 通过；subset-cardinality-typed: 通过；subset-equal-cardinality: 通过。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### R12：两个符号分数合并失败

- 分类：行为问题，根因暂定；主标签：`kernel_problem`；最早边界：proof search。
- 观察：b!=0、d!=0 可证 b*d!=0，但分数通分公式仍拒绝。
- 下一步：在分式目标的 WD/正规化/证据路径找首次失败，不能只补一个已经可证的乘积非零规则。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：fractions-combine**

```lit
forall a,b,c,d R:
    b!=0
    d!=0
    =>:
        a/b+c/d=(a*d+b*c)/(b*d)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "forall a, b, c, d R:\n    b != 0\n    d != 0\n    =>:\n        a / b + c / d = (a * d + b * c) / (b * d)", "why_failed": {"phase": "search_proof", "goal": "forall a, b, c, d R:\n    b != 0\n    d != 0\n    =>:\n        a / b + c / d = (a * d + b * c) / (b * d)"}, "stores": [], "infers": []}`。

对照：fraction-product-nonzero: 通过。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### R13：三角值不能消费符号约分结果

- 分类：行为问题，根因暂定；主标签：`kernel_problem`；最早边界：proof search。
- 观察：a!=0下 cos(a*pi/a+pi/2)=0 拒绝，cos(3*pi/2)=0通过。
- 下一步：核对带非零前提的有理式约分证据如何传给周期三角规则。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：cos-cancel**

```lit
have a R:
    a!=0
cos(a*pi/a+pi/2)=0
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "cos(a * pi / a + pi / 2) = 0", "why_failed": {"phase": "search_proof", "goal": "cos(a * pi / a + pi / 2) = 0"}, "stores": [], "infers": []}`。

对照：cos-literal: 通过。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### R14：let 捕获的数值在 builder/匿名调用中不可组合

- 分类：行为问题，根因暂定；主标签：`kernel_problem`；最早边界：WD / predicate domain / equality。
- 观察：let y=1 后 y in R 单独可证，但 builder WD 仍缺该证据；捕获 let y=3 的匿名函数等式拒绝，eval返回5；改用 typed have 的对照通过。
- 下一步：在 builder 的 predicate_domain 和匿名函数应用的载体/捕获值证据里比较 let 与 typed have。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：let-builder**

```lit
let y = 1
let A = {x R:x > y}
$is_set(A)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "let …", "why_failed": {"type": "define_obj", "rule_name": "Let binding", "message": "Bind a name to a well-defined value", "phase": "let", "failure": {"success": false, "obj": "{x R: x > y}", "phase": "well_defined", "failure": {"phase": "SetFormer", "failure": {"phase": "SetBuilder", "failure": {"phase": "fact", "failure": {"phase": "predicate_domain", "completed_requirements": [{"requirement": "x $in R", "verify": {"type": "atomic_except_equality", "success": true, "fact": "x $in R", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Identifier", "kind": "Identifier", "obj": "x"}, {"type": "by_known", "obj": "R", "wd_id": "wd2"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": {"type": "by_known_fact_domain", "cite": {"type": "by_known_atomic", "cite_fact_id": "f3", "why_parameters_of_known_fact_are_equal_…`。

**实际输入：let-anonymous**

```lit
let y=3
fn(x R) R{x+y}(2)=2+y
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "fn (x R) R{x + y}(2) = 2 + y", "why_failed": {"phase": "search_proof", "goal": "fn (x R) R{x + y}(2) = 2 + y"}, "stores": [], "infers": []}`。

对照：let-carrier: 通过；typed-builder: 通过；typed-anonymous: 通过；let-anonymous-eval: 通过，eval=5。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### R15：标量模板实例的 callable let 别名仍失败

- 分类：行为问题，根因暂定；主标签：`kernel_problem`；最早边界：well_defined / FnObj signature。
- 观察：直接 \identity<R>(2)=2通过，let f=\identity<R>;f(2)=2 的 WD 报 no matching function signature。新的 tuple 返回模板别名及 typed tuple 对照已通过。
- 下一步：检查标量模板的 alias signature 解析和证据；不再将已恢复的 tuple 路线笼统列为失败。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：template-alias**

```lit
template<S set>:
    have fn identity(x S) S=x
let f=\identity<R>
f(2)=2
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "f(2) = 2", "why_failed": {"phase": "search_proof", "goal": "f(2) = 2"}, "stores": [], "infers": []}`。

对照：template-direct: 通过；template-tuple-typed-alias: 通过。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### R16：tuple 算术的完整调用链不通过

- 分类：行为问题，根因暂定；主标签：`kernel_problem`；最早边界：proof search。
- 观察：add2((1,2),(3,4))=(1+3,2+4)=(4,6) 原样拒绝。
- 下一步：分开检查函数展开、投影值与最后的 tuple 坐标计算。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：add2-chain**

```lit
# Before: the full call timed out; literal projection carriers were unavailable.
# Now: unfold the function, prove coordinates, then calculate tuple entries.
# Gate: target/release/litex -strict -f examples/proof_nodes/equal/by_builtin_strategy/add2_calculation_chain.lit
have fn add2(u, v cart(R, R)) cart(R, R) = (u[1] + v[1], u[2] + v[2])
add2((1, 2), (3, 4)) = (1 + 3, 2 + 4) = (4, 6)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "add2((1, 2), (3, 4)) = (1 + 3, 2 + 4) = (4, 6)", "why_failed": {"phase": "search_proof", "goal": "add2((1, 2), (3, 4)) = (1 + 3, 2 + 4) = (4, 6)"}, "stores": [], "infers": []}`。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### A01：集合/区间的简短直断言仍需显式外延证明

- 分类：旧直接输入的自动化边界；主标签：`trust`；最早边界：proof search。
- 观察：原始集合相等直断言仍拒绝；若对应当前正例用显式证明通过，属于 authoring/自动化边界，不代表集合语义缺失。
- 下一步：使用所属正例中的已验证外延、成员和分情况接口；新增自动叶子需另行确定合同。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：historical-old-gap_gaps_cart__p04.lit**

```lit
# Intended valid regression: cart P04
cart({1}, {2}) = {(1, 2)}
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "cart({1}, {2}) = {(1, 2)}", "why_failed": {"phase": "search_proof", "goal": "cart({1}, {2}) = {(1, 2)}"}, "stores": [], "infers": []}`。

**实际输入：historical-old-gap_gaps_closed_range__p04.lit**

```lit
# Intended valid regression: closed_range P04
closed_range(-1, 1) = {-1, 0, 1}
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "closed_range(-1, 1) = {-1, 0, 1}", "why_failed": {"phase": "search_proof", "goal": "closed_range(-1, 1) = {-1, 0, 1}"}, "stores": [], "infers": []}`。

**实际输入：historical-old-gap_gaps_family_intersect__p01.lit**

```lit
# Intended valid regression: family_intersect P01
family_intersect({{1}}) = {1}
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "family_intersect({{1}}) = {1}", "why_failed": {"phase": "search_proof", "goal": "family_intersect({{1}}) = {1}"}, "stores": [], "infers": []}`。

**实际输入：historical-old-gap_gaps_family_intersect__p03.lit**

```lit
# Intended valid regression: family_intersect P03
family_intersect({{1}, {}}) = {}
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "family_intersect({{1}, {}}) = {}", "why_failed": {"phase": "search_proof", "goal": "family_intersect({{1}, {}}) = {}"}, "stores": [], "infers": []}`。

**实际输入：historical-old-gap_gaps_family_union__p05.lit**

```lit
# Intended valid regression: family_union P05
let U = family_union({{}, {1, 2}})
U = {1, 2}
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "U = {1, 2}", "why_failed": {"phase": "search_proof", "goal": "U = {1, 2}"}, "stores": [], "infers": []}`。

**实际输入：historical-old-gap_gaps_intersect__p01.lit**

```lit
# Intended valid regression: intersect P01
intersect({1, 2}, {2, 3}) = {2}
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "intersect({1, 2}, {2, 3}) = {2}", "why_failed": {"phase": "search_proof", "goal": "intersect({1, 2}, {2, 3}) = {2}"}, "stores": [], "infers": []}`。

**实际输入：historical-old-gap_gaps_list_set__p04.lit**

```lit
# Intended valid regression: list_set P04
{1, 2} = {2, 1}
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "{1, 2} = {2, 1}", "why_failed": {"phase": "search_proof", "goal": "{1, 2} = {2, 1}"}, "stores": [], "infers": []}`。

**实际输入：historical-old-gap_gaps_power_set__p06.lit**

```lit
# Intended valid regression: power_set P06
power_set(power_set({})) = {{}, {{}}}
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "power_set(power_set({})) = {{}, {{}}}", "why_failed": {"phase": "search_proof", "goal": "power_set(power_set({})) = {{}, {{}}}"}, "stores": [], "infers": []}`。

**实际输入：historical-old-gap_gaps_range__p04.lit**

```lit
# Intended valid regression: range P04
range(-2, 1) = {-2, -1, 0}
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "range(-2, 1) = {-2, -1, 0}", "why_failed": {"phase": "search_proof", "goal": "range(-2, 1) = {-2, -1, 0}"}, "stores": [], "infers": []}`。

**实际输入：historical-old-gap_gaps_set_minus__p01.lit**

```lit
# Intended valid regression: set_minus P01
set_minus({1, 2}, {2}) = {1}
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "set_minus({1, 2}, {2}) = {1}", "why_failed": {"phase": "search_proof", "goal": "set_minus({1, 2}, {2}) = {1}"}, "stores": [], "infers": []}`。

**实际输入：historical-old-gap_gaps_union__p01.lit**

```lit
# Intended valid regression: union P01
union({1}, {2}) = {1, 2}
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "union({1}, {2}) = {1, 2}", "why_failed": {"phase": "search_proof", "goal": "union({1}, {2}) = {1, 2}"}, "stores": [], "infers": []}`。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### A02：嵌套集合/tuple 构造缺自动互异证明

- 分类：旧直接输入的证明前提/自动化边界；主标签：`trust`；最早边界：well_defined / pairwise distinctness。
- 观察：构造{{1},{2}}等输入的 WD 要求元素互异；直接 tuple 非等式也拒绝。当前拥有者有显式反证路线。
- 下一步：先证明实际要求的元素互异，再构造外层集合；不要去掉 list-set 的 WD 要求。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：historical-old-gap_gaps_family_intersect__p02.lit**

```lit
# Intended valid regression: family_intersect P02
family_intersect({{1, 2}, {2, 3}}) = {2}
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "SetOperator", "failure": {"phase": "FamilyIntersect", "failure": {"phase": "child", "obj": "{{1, 2}, {2, 3}}", "failure": {"phase": "SetFormer", "failure": {"phase": "ListSet", "failure": {"phase": "requirement", "obj": "{{1, 2}, {2, 3}}", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{1, 2} != {2, 3}", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{1, 2}", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}, {"type": "by_def", "family": "Literal", "kind": "Number", "obj": "2"}], "requirement_fact_verified": [{"type": "atomic_except_e…`。

**实际输入：historical-old-gap_gaps_family_intersect__p04.lit**

```lit
# Intended valid regression: family_intersect P04
let I = family_intersect({{1}, {2}})
I = I
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "let …", "why_failed": {"type": "define_obj", "rule_name": "Let binding", "message": "Bind a name to a well-defined value", "phase": "let", "failure": {"success": false, "obj": "family_intersect({{1}, {2}})", "phase": "well_defined", "failure": {"phase": "SetOperator", "failure": {"phase": "FamilyIntersect", "failure": {"phase": "child", "obj": "{{1}, {2}}", "failure": {"phase": "SetFormer", "failure": {"phase": "ListSet", "failure": {"phase": "requirement", "obj": "{{1}, {2}}", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{1} != {2}", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{1}", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}], "requirement_fact_verified": []}, {"type": "by_d…`。

**实际输入：historical-old-gap_gaps_family_union__p03.lit**

```lit
# Intended valid regression: family_union P03
family_union({{1}, {2}}) = {1, 2}
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "SetOperator", "failure": {"phase": "FamilyUnion", "failure": {"phase": "child", "obj": "{{1}, {2}}", "failure": {"phase": "SetFormer", "failure": {"phase": "ListSet", "failure": {"phase": "requirement", "obj": "{{1}, {2}}", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{1} != {2}", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{1}", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}], "requirement_fact_verified": []}, {"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{2}", "child_obj_well_defined": [{"type": "by_de…`。

**实际输入：historical-old-gap_gaps_family_union__p04.lit**

```lit
# Intended valid regression: family_union P04
1 $in family_union({{1}, {2}})
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "atomic_except_equality", "success": false, "phase": "well_defined", "failure": {"phase": "SetOperator", "failure": {"phase": "FamilyUnion", "failure": {"phase": "child", "obj": "{{1}, {2}}", "failure": {"phase": "SetFormer", "failure": {"phase": "ListSet", "failure": {"phase": "requirement", "obj": "{{1}, {2}}", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{1} != {2}", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{1}", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}], "requirement_fact_verified": []}, {"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{2}", "child_obj_well_defined": [{…`。

**实际输入：historical-old-gap_gaps_finite_set_size__p05.lit**

```lit
# Intended valid regression: finite_set_size P05
finite_set_size({{1}, {2}}) = 2
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "FiniteSetStat", "failure": {"phase": "FiniteSetSize", "failure": {"phase": "child", "obj": "{{1}, {2}}", "failure": {"phase": "SetFormer", "failure": {"phase": "ListSet", "failure": {"phase": "requirement", "obj": "{{1}, {2}}", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{1} != {2}", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{1}", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}], "requirement_fact_verified": []}, {"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{2}", "child_obj_well_defined": [{"type": "b…`。

**实际输入：historical-old-gap_gaps_list_set__p06.lit**

```lit
# Intended valid regression: list_set P06
{1} $in {{1}, {2}}
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "atomic_except_equality", "success": false, "phase": "well_defined", "failure": {"phase": "SetFormer", "failure": {"phase": "ListSet", "failure": {"phase": "requirement", "obj": "{{1}, {2}}", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{1} != {2}", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{1}", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}], "requirement_fact_verified": []}, {"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{2}", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "2"}], "requirement_fact_verified": []}], "predicate_signat…`。

**实际输入：historical-old-gap_gaps_list_set__p07.lit**

```lit
# Intended valid regression: list_set P07
(1, 2) $in {(1, 2), (2, 1)}
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "atomic_except_equality", "success": false, "phase": "well_defined", "failure": {"phase": "SetFormer", "failure": {"phase": "ListSet", "failure": {"phase": "requirement", "obj": "{(1, 2), (2, 1)}", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "(1, 2) != (2, 1)", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "ProductShape", "kind": "Tuple", "obj": "(1, 2)", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}, {"type": "by_def", "family": "Literal", "kind": "Number", "obj": "2"}], "requirement_fact_verified": []}, {"type": "by_def", "family": "ProductShape", "kind": "Tuple", "obj": "(2, 1)", "child_obj_well_defined": [{"type": "by_def", "family": "Lit…`。

**实际输入：historical-old-gap_gaps_tuple__p06.lit**

```lit
# Intended valid regression: tuple P06
(1, 2) != (2, 1)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "(1, 2) != (2, 1)", "why_failed": {"phase": "search_proof", "goal": "(1, 2) != (2, 1)"}, "stores": [], "infers": []}`。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### A03：嵌套函数与 tuple 投影直断言仍需中间等式

- 分类：旧直接输入的逐层展开边界；主标签：`trust`；最早边界：proof search。
- 观察：f(f(1))、curried call、两层tuple下标及投影后的数值简算直断言拒绝；保留当前文件中的逐层等式展开。
- 下一步：比较明确展开后的接受路线，区分深层自动化边界和现存局部证明链的回归。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：historical-old-gap_gaps_fn_obj__p05.lit**

```lit
# Intended valid regression: fn_obj P05
have fn f(x R) R = x + 1
f(f(1)) = 3
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "f(f(1)) = 3", "why_failed": {"phase": "search_proof", "goal": "f(f(1)) = 3"}, "stores": [], "infers": []}`。

**实际输入：historical-old-gap_gaps_fn_obj__p06.lit**

```lit
# Intended valid regression: fn_obj P06
have fn f(x R) fn(y R) R = fn(y R) R {x + y}
f(2)(3) = 5
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "f(2)(3) = 5", "why_failed": {"phase": "search_proof", "goal": "f(2)(3) = 5"}, "stores": [], "infers": []}`。

**实际输入：historical-old-gap_gaps_obj_at_index__p04.lit**

```lit
# Intended valid regression: obj_at_index P04
((1, 2), 3)[1][2] = 2
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "ProductShape", "failure": {"phase": "ObjAtIndex", "failure": {"phase": "requirement", "obj": "((1, 2), 3)[1][2]", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "$is_tuple(((1, 2), 3)[1])", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "ProductShape", "kind": "ObjAtIndex", "obj": "((1, 2), 3)[1]", "obj_well_defined": {"type": "by_def", "family": "ProductShape", "kind": "Tuple", "obj": "((1, 2), 3)", "child_obj_well_defined": [{"type": "by_def", "family": "ProductShape", "kind": "Tuple", "obj": "(1, 2)", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}, {"type": "by_def", "…`。

**实际输入：historical-old-gap_gaps_obj_at_index__p06.lit**

```lit
# Intended valid regression: obj_at_index P06
(2 + 3, 4 * 2)[2] = 8
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "(2 + 3, 4 * 2)[2] = 8", "why_failed": {"phase": "search_proof", "goal": "(2 + 3, 4 * 2)[2] = 8"}, "stores": [], "infers": []}`。

**实际输入：historical-old-gap_gaps_tuple__p04.lit**

```lit
# Intended valid regression: tuple P04
((1, 2), 3)[1][2] = 2
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "ProductShape", "failure": {"phase": "ObjAtIndex", "failure": {"phase": "requirement", "obj": "((1, 2), 3)[1][2]", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "$is_tuple(((1, 2), 3)[1])", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "ProductShape", "kind": "ObjAtIndex", "obj": "((1, 2), 3)[1]", "obj_well_defined": {"type": "by_def", "family": "ProductShape", "kind": "Tuple", "obj": "((1, 2), 3)", "child_obj_well_defined": [{"type": "by_def", "family": "ProductShape", "kind": "Tuple", "obj": "(1, 2)", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}, {"type": "by_def", "…`。

**实际输入：named-nested_addition_associativity**

```lit
forall a, b, c Z:
    fn(x, y Z) Z {x + y}(fn(x, y Z) Z {x + y}(a, b), c) = fn(x, y Z) Z {x + y}(a, fn(x, y Z) Z {x + y}(b, c))
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "forall a, b, c Z:\n    fn (x, y Z) Z{x + y}(fn (x, y Z) Z{x + y}(a, b), c) = fn (x, y Z) Z{x + y}(a, fn (x, y Z) Z{x + y}(b, c))", "why_failed": {"phase": "search_proof", "goal": "forall a, b, c Z:\n    fn (x, y Z) Z{x + y}(fn (x, y Z) Z{x + y}(a, b), c) = fn (x, y Z) Z{x + y}(a, fn (x, y Z) Z{x + y}(b, c))"}, "stores": [], "infers": []}`。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### A04：函数像、序列载体和索引集合的直接接口仍受限

- 分类：旧直接输入的载体/定义消费边界；主标签：`trust`；最早边界：proof search。
- 观察：函数像=R、匿名函数属于seq/finite_seq、range非成员及 singleton index family 的原直写法拒绝。
- 下一步：按每项记录的第一条 WD/搜索要求，优先使用对应当前正例的载体、成员和定义证明步骤。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：historical-old-gap_gaps_finite_seq_set__p05.lit**

```lit
# Intended valid regression: finite_seq_set P05
fn(x closed_range(1, 2)) R {x} $in finite_seq(R, 2)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "fn (x closed_range(1, 2)) R{x} $in finite_seq(R, 2)", "why_failed": {"phase": "search_proof", "goal": "fn (x closed_range(1, 2)) R{x} $in finite_seq(R, 2)"}, "stores": [], "infers": []}`。

**实际输入：historical-old-gap_gaps_fn_range__p02.lit**

```lit
# Intended valid regression: fn_range P02
fn_range(fn(x R) R {x}) = R
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "fn_range(fn (x R) R{x}) = R", "why_failed": {"phase": "search_proof", "goal": "fn_range(fn (x R) R{x}) = R"}, "stores": [], "infers": []}`。

**实际输入：historical-old-gap_gaps_index_intersect__p02.lit**

```lit
# Intended valid regression: index_intersect P02
have fn A(k {1}) power_set(N) = {k}
index_intersect({1}, N, A) = {1}
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "have fn …", "why_failed": {"type": "define_fn", "rule_name": "Have function equal", "message": "Define a named function equal to an anonymous function", "phase": "have_fn_equal", "failure": {"success": false, "obj": "fn (k {1}) power_set(N){{k}}", "phase": "well_defined", "failure": {"phase": "FunctionSpace", "failure": {"phase": "AnonymousFn", "failure": {"phase": "body_in_return_set", "failure": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{k} $in power_set(N)", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{k}", "child_obj_well_defined": [{"type": "by_def", "family": "Identifier", "kind": "Identifier", "obj": "k"}], "requirement_fact_verified": []}, {"type": "by_def", "family": "SetOperator", "kind": "PowerSet", "obj": "power_set(N)", "c…`。

**实际输入：historical-old-gap_gaps_index_union__p02.lit**

```lit
# Intended valid regression: index_union P02
have fn A(k {1}) power_set(N) = {k}
index_union({1}, N, A) = {1}
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "have fn …", "why_failed": {"type": "define_fn", "rule_name": "Have function equal", "message": "Define a named function equal to an anonymous function", "phase": "have_fn_equal", "failure": {"success": false, "obj": "fn (k {1}) power_set(N){{k}}", "phase": "well_defined", "failure": {"phase": "FunctionSpace", "failure": {"phase": "AnonymousFn", "failure": {"phase": "body_in_return_set", "failure": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{k} $in power_set(N)", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{k}", "child_obj_well_defined": [{"type": "by_def", "family": "Identifier", "kind": "Identifier", "obj": "k"}], "requirement_fact_verified": []}, {"type": "by_def", "family": "SetOperator", "kind": "PowerSet", "obj": "power_set(N)", "c…`。

**实际输入：historical-old-gap_gaps_range__p06.lit**

```lit
# Intended valid regression: range P06
not 3 $in range(1, 3)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "not 3 $in range(1, 3)", "why_failed": {"phase": "search_proof", "goal": "not 3 $in range(1, 3)"}, "stores": [], "infers": []}`。

**实际输入：historical-old-gap_gaps_seq_set__p03.lit**

```lit
# Intended valid regression: seq_set P03
fn(x N+) N {x} $in seq(N)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "fn (x N+) N{x} $in seq(N)", "why_failed": {"phase": "search_proof", "goal": "fn (x N+) N{x} $in seq(N)"}, "stores": [], "infers": []}`。

**实际输入：historical-old-gap_gaps_seq_set__p04.lit**

```lit
# Intended valid regression: seq_set P04
fn(x N+) R {0} $in seq(R)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "fn (x N+) R{0} $in seq(R)", "why_failed": {"phase": "search_proof", "goal": "fn (x N+) R{0} $in seq(R)"}, "stores": [], "infers": []}`。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### A05：反三角特殊值及一般 log 的直写法仍受限

- 分类：旧直接输入的前提/自动化边界；主标签：`trust`；最早边界：proof search。
- 观察：arctan(±1)、arccot(±1)、log(e,e)=1及幂-对数复合直断言拒绝；先证明 log(2,2^x)=x 的对照通过。
- 下一步：分别核对主值区间、e的载体/非单位要求和内层log证据；复用已验证的显式步。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：historical-old-gap_gaps_arccot__p02.lit**

```lit
# Intended valid regression: arccot P02
arccot(1) = pi / 4
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "arccot(1) = pi / 4", "why_failed": {"phase": "search_proof", "goal": "arccot(1) = pi / 4"}, "stores": [], "infers": []}`。

**实际输入：historical-old-gap_gaps_arccot__p04.lit**

```lit
# Intended valid regression: arccot P04
arccot(-1) = 3 * pi / 4
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "arccot(-1) = 3 * pi / 4", "why_failed": {"phase": "search_proof", "goal": "arccot(-1) = 3 * pi / 4"}, "stores": [], "infers": []}`。

**实际输入：historical-old-gap_gaps_arctan__p02.lit**

```lit
# Intended valid regression: arctan P02
arctan(1) = pi / 4
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "arctan(1) = pi / 4", "why_failed": {"phase": "search_proof", "goal": "arctan(1) = pi / 4"}, "stores": [], "infers": []}`。

**实际输入：historical-old-gap_gaps_arctan__p03.lit**

```lit
# Intended valid regression: arctan P03
arctan(-1) = -pi / 4
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "arctan(-1) = -pi / 4", "why_failed": {"phase": "search_proof", "goal": "arctan(-1) = -pi / 4"}, "stores": [], "infers": []}`。

**实际输入：historical-old-gap_gaps_log__p06.lit**

```lit
# Intended valid regression: log P06
log(e, e) = 1
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "ExpLogOperator", "failure": {"phase": "Log", "failure": {"phase": "requirement", "obj": "log (e, e)", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "e != 1", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Literal", "kind": "EulerNumber", "obj": "e"}, {"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}}}}}}}, "stores": [], "infers": []}`。

**实际输入：named-pow_log_direct**

```lit
have x N
2^(log(2, 2^x)) = 2^x
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "ArithmeticOperator", "failure": {"phase": "Pow", "failure": {"phase": "requirement", "obj": "2 ^ log (2, 2 ^ x)", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "log (2, 2 ^ x) $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "ExpLogOperator", "kind": "Log", "obj": "log (2, 2 ^ x)", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "2"}, {"type": "by_def", "family": "ArithmeticOperator", "kind": "Pow", "obj": "2 ^ x", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "2"}, {"type": "by_def", "family": "Identifier", "kind": "Identifi…`。

**实际输入：named-pow_log_order_bridge**

```lit
have x N
2^x > 0
2^(log(2, 2^x)) = 2^x
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "ArithmeticOperator", "failure": {"phase": "Pow", "failure": {"phase": "requirement", "obj": "2 ^ log (2, 2 ^ x)", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "log (2, 2 ^ x) $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "ExpLogOperator", "kind": "Log", "obj": "log (2, 2 ^ x)", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "2"}, {"type": "by_known", "obj": "2 ^ x", "wd_id": "wd3"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "2 $in R", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Li…`。

**实际输入：named-pow_log_positive_bridge**

```lit
have x N
2^x $in R+
2^(log(2, 2^x)) = 2^x
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "ArithmeticOperator", "failure": {"phase": "Pow", "failure": {"phase": "requirement", "obj": "2 ^ log (2, 2 ^ x)", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "log (2, 2 ^ x) $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "ExpLogOperator", "kind": "Log", "obj": "log (2, 2 ^ x)", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "2"}, {"type": "by_known", "obj": "2 ^ x", "wd_id": "wd3"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fact": "2 $in R", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Li…`。

对照：pow-log-bridge: 通过。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### A06：跨模块算术原文件缺定义释放

- 分类：已验证的例子迁移路径，原文件尚未迁移；主标签：`trust`；最早边界：WD / imported definitions。
- 观察：原文件直接引用gf的值，在算术WD和投影/维数消费上失败；独立临时模块使用同一gf依赖并先release obj def，四个原目标通过。
- 下一步：迁移原调用文件到已有的显式定义释放接口；不能将未知模块的 -e 失败当成内核问题。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：current-file-examples/module_manager/import_alias_qualified_arithmetic/main.lit**

```lit
# Tracer: persistent dependencies belong to litex.config, not Litex source.
#
# Before:
# import "../../_internal/fixtures/geometry_foundation" as gf
# Former behavior: an isolated .lit file could mutate the module graph while statements executed.
#
# Now: the adjacent litex.config owns the gf dependency, so this source contains only Litex
# statements and qualified mathematical references.

gf::main::a + gf::main::a = gf::main2::b
gf::main::pair[1] = 3
gf::main2::pair[1] = 8
cart_dim(gf::main::ProductSet) = 2

# Current behavior: project execution discovers gf before parsing this file. An interactive REPL may
# issue the same import as a terminal command, which mutates only its ephemeral in-memory manifest.
#
# Boundary: uncommenting the old import line is rejected in every .lit source, including
# `litex -isolated -f`; unknown qualified names such as gf::main::missing remain rejected.
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "ArithmeticOperator", "failure": {"phase": "Add", "failure": {"phase": "requirement", "obj": "m0::f0::a + m0::f0::a", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "m0::f0::a $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Identifier", "kind": "Identifier", "obj": "m0::f0::a"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}}}}}}}, "stores": [], "infers": []}`。

对照：qualified-registered-release-control: 通过。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### S01：线性代数 showcase 的 kernel 定义等式失败

- 分类：行为问题，根因暂定；主标签：`kernel_problem`；最早边界：theorem proof_body / equality。
- 观察：最早失败已前移/变化：当前是 kernel={x V:T(x)=target.zero} 的搜索，原先neg模板调用WD已过。
- 下一步：在 linear_map_kernel_is_subspace 的 linear_kernel 模板、let结果和builder等式中查实际定义证据。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：showcase-linear**

```lit
thm linear_map_kernel_is_subspace:
    ? forall K nonempty_set, field &Field<K>, V nonempty_set, W nonempty_set, source &VectorSpace<K, field, V>, target &VectorSpace<K, field, W>, T fn(v V) W:
        $is_linear_map(K, field, V, W, source, target, T)
        =>:
            $is_subspace(K, field, V, source, \linear_kernel<V, W, target.zero, T>)
    let kernel = \linear_kernel<V, W, target.zero, T>
    by thm linear_map_sends_zero_to_zero(K, field, V, W, source, target, T) => T(source.zero) = target.zero
    kernel = {x V: T(x) = target.zero}
    by thm set_builder_member(source.zero, {x V: T(x) = target.zero}) => source.zero $in {x V: T(x) = target.zero}
    source.zero $in kernel
    claim:
        ? forall u, v V:
            u $in kernel
            v $in kernel
            =>:
                source.add(u, v) $in kernel
        u $in {x V: T(x) = target.zero}
        T(u) = target.zero
        v $in {x V: T(x) = target.zero}
        T(v) = target.zero
        T(source.add(u, v)) = target.add(T(u), T(v)) = target.add(target.zero, target.zero) = target.zero
        by thm set_builder_member(source.add(u, v), {x V: T(x) = target.zero}) => source.add(u, v) $in {x V: T(x) = target.zero}
        source.add(u, v) $in kernel
    claim:
        ? forall a K, v V:
            v $in kernel
            =>:
                source.smul(a, v) $in kernel
        v $in {x V: T(x) = target.zero}
        T(v) = target.zero
        by thm scalar_times_zero_vector(K, field, W, target, a) => target.smul(a, target.zero) = target.zero
        T(source.smul(a, v)) = target.smul(a, T(v)) = target.smul(a, target.zero) = target.zero
        by thm set_builder_member(source.smul(a, v), {x V: T(x) = target.zero}) => source.smul(a, v) $in {x V: T(x) = target.zero}
        source.smul(a, v) $in kernel
    by def $is_subspace(K, field, V, source, \linear_kernel<V, W, target.zero, T>)

# Injectivity turns T(x)=0=T(0) into x=0, proving kernel(T)={0}.
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "thm", "why_failed": {"type": "definition", "rule_name": "Define theorem", "message": "Record a theorem", "phase": "def_thm", "failure": {"phase": "proof_body", "index": 2, "result": {"success": false, "kind": "fact", "statement": "kernel = {x V: T(x) = target.zero}", "verify": {"type": "equality", "success": false, "phase": "search_proof", "fact": "kernel = {x V: T(x) = target.zero}", "well_defined": {"left": {"type": "by_def", "family": "Identifier", "kind": "Identifier", "obj": "kernel"}, "right": {"type": "by_def", "family": "SetFormer", "kind": "SetBuilder", "obj": "{x V: T(x) = target.zero}", "param_set_well_defined": {"type": "by_def", "family": "Identifier", "kind": "Identifier", "obj": "V"}, "fact_well_defined": [{"type": "equality", "proof": {"left": {"type": "by_def", "family": "FnObj", "kind": "FnObj", "obj": "T(x)", "child_obj_well_defined": […`。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### S02：拓扑 showcase 按定义完成连续性失败

- 分类：行为问题，根因暂定；主标签：`kernel_problem`；最早边界：theorem proof_body / by_def。
- 观察：continuous_composition 内两个前置claim之后，最后按定义证明 is_continuous 的步骤拒绝；下游主定理没有执行。
- 下一步：从记录的首个失败定理及 by_def 目标检查对应predicate的定义要求和可用成员证据。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：showcase-topology**

```lit
thm continuous_composition:
    ? forall A set, open_sets_A power_set(power_set(A)), B set, open_sets_B power_set(power_set(B)), CarrierC set, open_sets_C power_set(power_set(CarrierC)), f fn(x A) B, g fn(y B) CarrierC:
        $ContinuousCompositionSetting(A, open_sets_A, B, open_sets_B, CarrierC, open_sets_C, f, g)
        =>:
            $is_continuous(A, open_sets_A, CarrierC, open_sets_C, fn(x A) CarrierC {g(f(x))})
    claim:
        ? forall target_open open_sets_C:
            {x A: g(f(x)) $in target_open} $in open_sets_A
        {y B: g(y) $in target_open} $in open_sets_B
        have middle_open open_sets_B = {y B: g(y) $in target_open}
        {x A: f(x) $in middle_open} $in open_sets_A
        have nested_preimage open_sets_A = {x A: f(x) $in middle_open}
        have direct_preimage power_set(A) = {x A: g(f(x)) $in target_open}
        claim:
            ? nested_preimage $subset direct_preimage
            claim:
                ? forall point nested_preimage:
                    point $in direct_preimage
                f(point) $in middle_open
                g(f(point)) $in target_open
                by thm set_builder_member(point, {x A: g(f(x)) $in target_open}) => point $in {x A: g(f(x)) $in target_open}
            by def:
                ? nested_preimage $subset direct_preimage
        claim:
            ? direct_preimage $subset nested_preimage
            claim:
                ? forall point direct_preimage:
                    point $in nested_preimage
                g(f(point)) $in target_open
                by thm set_builder_member(f(point), {y B: g(y) $in target_open}) => f(point) $in {y B: g(y) $in target_open}
                f(point) $in middle_open
                by thm set_builder_member(point, {x A: f(x) $in middle_open}) => point $in {x A: f(x) $in middle_open}
            by def:
                ? direct_preimage $subset nested_preimage
        by extension:
            ? nested_preimage = direct_preimage
        direct_preimage $in open_sets_A
    claim:
        ? forall target_open open_sets_C:
            {candidate A: fn(argument A) CarrierC {g(f(argument))}(candidate) $in target_open} $in open_sets_A
        have direct_preimage open_sets_A = {candidate A: g(f(candidate)) $in target_open}
        have literal_preimage power_set(A) = {candidate A: fn(argument A) CarrierC {g(f(argument))}(candidate) $in target_open}
        claim:
            ? literal_preimage $subset direct_preimage
            claim:
                ? forall point literal_preimage:
                    point $in direct_preimage
                fn(argument A) CarrierC {g(f(argument))}(point) = g(f(point))
                g(f(point)) $in target_open
                by thm set_builder_member(point, {candidate A: g(f(candidate)) $in target_open}) => point $in {candidate A: g(f(candidate)) $in target_open}
            by def:
                ? literal_preimage $subset direct_preimage
        claim:
            ? direct_preimage $subset literal_preimage
            claim:
                ? forall point direct_preimage:
                    point $in literal_preimage
                g(f(point)) $in target_open
                fn(argument A) CarrierC {g(f(argument))}(point) = g(f(point))
                fn(argument A) CarrierC {g(f(argument))}(point) $in target_open
                by thm set_builder_member(point, {candidate A: fn(argument A) CarrierC {g(f(argument))}(candidate) $in target_open}) => point $in {candidate A: fn(argument A) CarrierC {g(f(argument))}(candidate) $in target_open}
            by def:
                ? direct_preimage $subset literal_preimage
        by extension:
            ? literal_preimage = direct_preimage
        literal_preimage $in open_sets_A
    by def:
        ? $is_continuous(A, open_sets_A, CarrierC, open_sets_C, fn(x A) CarrierC {g(f(x))})

prop is_closed(X set, open_sets power_set(power_set(X)), F power_set(X)):
    $TopologicalSpaceSetting(X, open_sets)
    set_minus(X, F) $in open_sets

prop has_closed_preimages(X set, open_sets_X power_set(power_set(X)), Y set, open_sets_Y power_set(power_set(Y)), f fn(x X) Y):
    $TopologicalMapSetting(X, open_sets_X, Y, open_sets_Y, f)
    forall F power_set(Y):
        $is_closed(Y, open_sets_Y, F)
        =>:
            $is_closed(X, open_sets_X, {x X: f(x) $in F})

# 首个后续失败为by_def；完整前缀与结果在receipt。
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "thm", "why_failed": {"type": "definition", "rule_name": "Define theorem", "message": "Record a theorem", "phase": "def_thm", "failure": {"phase": "proof_body", "index": 2, "result": {"success": false, "kind": "by_def"}}}, "stores": [], "infers": []}`。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### S03：Newton showcase 函数返回正数的 WD 失败

- 分类：行为问题，根因暂定；主标签：`kernel_problem`；最早边界：well_defined / body_in_return_set。
- 观察：have fn 的返回载体 R+ 中，(x+2/x)/2 in R+ 无法证明；不是数值计算溢出。
- 下一步：分别检查正数除法、加法、再次除法的载体证据及实际搜索入口。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：showcase-newton**

```lit
# Numerical analysis in Litex: Newton's method for sqrt(2).
#
# Included: the Newton update, a checked executable step, a recursive iterate,
# residual gaps, the exact one-step gap identity, quadratic contraction, and a
# closed-form error bound.
#
# Write x_n for sqrt_two_newton_iterate(n) and
# g_n for the residual gap abs(x_n^2 - 2).
#
# Main line:
#
#   4 * x_n^2 * g_(n+1) = g_n^2
#                         =>
#   g_(n+1) <= g_n^2 / 4
#                         =>
#   g_n <= 4 * (1 / 4)^(2^n)
#
# Thus the central result is a per-step quadratic contraction of the
# residual gap. The final closed-form estimate is its corollary.

# Definitions and a concrete preview.
have fn square_root_two_residual(x R) R = x^2 - 2
have fn newton_sqrt_two(x R+) R+ = (x + 2 / x) / 2

# The proved iteration stays positive, so it never uses the zero branch. This
# explicit restart makes the same single-step formula total on R for the
# experimental Python extractor without changing the mathematical update.
# One `algo … by cases` defines the mathematical fn and the extractable cases.
# (Replaced removed `have fn` + `have algo for` pair.)
# [-extract]
algo newton_sqrt_two_step(x R) R by cases:
    case x = 0: 1
    case x != 0: (x + 2 / x) / 2
# [end of -extract]

claim:
    ? forall x R+:
        newton_sqrt_two_step(x) = newton_sqrt_two(x)
    0 < x
    x != 0
    newton_sqrt_two_step(x) = (x + 2 / x) / 2 = newton_sqrt_two(x)

have fn sqrt_two_newton_iterate(n N) R+ by induc n from 0:
    case n = 0: 1
    case n > 0: newton_sqrt_two(sqrt_two_newton_iterate(n - 1))

have fn sqrt_two_newton_gap(n N) R = abs(square_root_two_residual(sqrt_two_newton_iterate(n)))

# This comparison sequence is chosen to obey B_(n+1) = B_n^2 / 4.
thm sqrt_two_newton_gap_bound_positive:
    ? forall n N:
        4 * (1 / 4)^(2^n) $in R+
    2^n $in R
    1 / 4 > 0
    (1 / 4)^(2^n) > 0
    4 * (1 / 4)^(2^n) > 0

have fn sqrt_two_newton_gap_bound(n N) R+ = 4 * (1 / 4)^(2^n)

newton_sqrt_two(1) = 3 / 2
newton_sqrt_two(3 / 2) = ((3 / 2) + 2 / (3 / 2)) / 2 = 17 / 12
square_root_two_residual(1) = -1
square_root_two_residual(3 / 2) = 1 / 4
square_root_two_residual(17 / 12) = (17 / 12)^2 - 2 = 1 / 144

thm sqrt_two_newton_iterate_step:
    ? forall n N:
        sqrt_two_newton_iterate(n + 1) = newton_sqrt_two(sqrt_two_newton_iterate(n))
    n + 1 > 0
    (n + 1) - 1 = n
    sqrt_two_newton_iterate(n + 1) = newton_sqrt_two(sqrt_two_newton_iterate((n + 1) - 1))
    sqrt_two_newton_iterate((n + 1) - 1) = sqrt_two_newton_iterate(n)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`{"success": false, "statement": "have fn …", "why_failed": {"type": "define_fn", "rule_name": "Have function equal", "message": "Define a named function equal to an anonymous function", "phase": "have_fn_equal", "failure": {"success": false, "obj": "fn (x R+) R+{(x + 2 / x) / 2}", "phase": "well_defined", "failure": {"phase": "FunctionSpace", "failure": {"phase": "AnonymousFn", "failure": {"phase": "body_in_return_set", "failure": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "(x + 2 / x) / 2 $in R+", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "ArithmeticOperator", "kind": "Div", "obj": "(x + 2 / x) / 2", "child_obj_well_defined": [{"type": "by_def", "family": "ArithmeticOperator", "kind": "Add", "obj": "x + 2 / x", "child_obj_well_defined": [{"type": "by_def", "family": "Identifier", "kind": "Identifier", "obj…`。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### T01：fn_set 正例自身无效，合法 dependent codomain 也尚不能解析

- 分类：正例建模错误 + 合法依赖返回集合的解析能力边界；主标签：`trust`；最早边界：parse / return binder。
- 观察：现存 P04 fn(x R)x 既报undefined x，也把实数x当返回集合；合法集合值参数 fn(x power_set(R))x 同样报undefined x。
- 下一步：先修正正例的数学类型定位；若要支持合法 dependent codomain，再讨论现有 fn 接口对返回绑定的合同。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：fn_set-P04**

```lit
sketch:
    let F = fn(x R) x
    $is_set(F)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`"Runtime(ParseError(RuntimeParseError { message: \"undefined name `x`\", line: 2, path: Eval }))"`。

**实际输入：dependent-legitimate**

```lit
let F=fn(x power_set(R))x
$is_set(F)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`"Runtime(ParseError(RuntimeParseError { message: \"undefined name `x`\", line: 1, path: Eval }))"`。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### T02：单字段 struct 是现行明确限制

- 分类：有意保留的语法/表示限制及未迁移例子；主标签：`trust`；最早边界：parse。
- 观察：parser 明确要求至少两个字段；旧 alias 示例仍含单字段 ScalarOps/Space，整文件先解析失败，不能沿用旧的首个WD失败描述。
- 下一步：把公开例子与现行struct合同对齐；是否支持单字段是独立语义/表示决定，本次未实现。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：single-field**

```lit
struct ScalarOps:
    add fn(x,y R)R
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`"Runtime(ParseError(RuntimeParseError { message: \"struct definition expects at least two fields\", line: 1, path: Eval }))"`。

**实际输入：named-single_field_struct**

```lit
struct ScalarOps:
    add fn(x, y R) R
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`"Runtime(ParseError(RuntimeParseError { message: \"struct definition expects at least two fields\", line: 1, path: Eval }))"`。

**实际输入：current-file-examples/stmt_nodes/definition/let_template_struct_aliases.lit**

```lit
# Stmt: let + template + struct alias composition
# Run: litex -f examples/stmt_nodes/definition/let_template_struct_aliases.lit
#
# `let` composes with `template` at two useful levels. The template below
# returns a parameterized struct, so the example also exposes the carrier
# boundary of a transparent abbreviation.

struct Triple<X set>:
    first X
    second X
    third X

template<X set>:
    have fn triple(a, b, c X) &Triple<X> = (a, b, c)

# Fix the template parameter and retain the ordinary function parameters.
let triple_R = \triple<R>

# Fix the complete application result.
let chosen = \triple<R>(1, 2, 3)

triple_R(4, 5, 6) = (4, 5, 6)
chosen = (1, 2, 3)

# `let` stores a transparent equality but does not create carrier evidence.
# Introduce a typed object only when later mathematics needs struct fields.
have chosen_struct &Triple<R> = chosen
chosen_struct.first = 1

# These remain outside the current field-access boundary because neither let
# name owns a direct struct carrier:
# triple_R(4, 5, 6).first = 4
# chosen.first = 1

# A `let` may also name a callable field reached through a nested struct. The
# verifier derives the retained `(x, y R) -> R` contract from the field-access
# object's frozen `ScalarOps` view; `scalar_add` is still only a transparent
# local abbreviation, not a second function declaration.
struct ScalarOps:
    add fn(x, y R) R

struct Space:
    scalars &ScalarOps

thm callable_struct_field_alias:
    ? forall space &Space, x, y R:
        space.scalars.add(x, y) = space.scalars.add(x, y)
    let scalar_add = space.scalars.add
    scalar_add(x, y) = space.scalars.add(x, y)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`"Runtime(ParseError(RuntimeParseError { message: \"struct definition expects at least two fields\", line: 39, path: Real(\"/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-04/remaining-issues-audit/snapshot/examples/stmt_nodes/definition/let_template_struct_aliases.lit\") }))"`。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### T03：旧模板 guard 探针的写法不符合当前解析

- 分类：旧语法探针/用例问题；主标签：`trust`；最早边界：parse。
- 观察：template<S set,bound R:bound>0>: 目前parse报 expected object, got colon；该旧探针不能证明全部模板guard功能坏了。
- 下一步：核对已通过guard用例的现行header语法；先改正测试输入，再检查权限/guard证据。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：template-guard-syntax**

```lit
template<S set,bound R:bound>0>:
    have fn positive_pair(x N:x>0)cart(N,N)=(x,x)
```

实际结果：`success=false`，exit `1`。
最早失败记录（完整见机器记录/receipt）：`"Runtime(ParseError(RuntimeParseError { message: \"expected object, got `:`\", line: 1, path: Eval }))"`。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### T04：旧输出和计算结果表示断言过时

- 分类：测试维护问题；主标签：`trust`；最早边界：evidence/output assertions。
- 观察：6个Rust断言属于成功后的旧路线/表示期望：数值模/周期/有理数等转closed calculation；eval sqrt(0.36)返回3/5；sqrt(2)可精确返回sqrt(2)；字段载体证据名称变化。
- 下一步：按现行语义及证据合同更新这些断言；不要把已成功的数学目标列为计算失败。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：old-decimal**

```lit
2.400 = 2.4
```

实际结果：`success=true`，exit `0`。

**实际输入：field-codomain-file**

```lit
# Showcase migration regression: verified without trust.
# Run: target/release/litex -strict -f examples/wd/field_application_codomain.lit
# The declared signature also supplies closure inside another field call.
struct Operation<A nonempty_set>:
    zero A
    add fn(x, y A) A

thm nested_generic_call:
    ? forall A nonempty_set, s &Operation<A>, a, b, c A:
        s.add(s.add(a, b), c) $in A

struct Outer<A nonempty_set>:
    operation &Operation<A>
    tag N

thm nested_receiver:
    ? forall s &Outer<R>:
        s.operation.add(s.operation.add(0, 1), 2) $in R

# Field carriers must also be available for arguments such as s.zero.
thm zero_argument:
    ? forall A nonempty_set, s &Operation<A>, x A:
        s.add(s.zero, x) $in A
```

实际结果：`success=true`，exit `0`。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

旧断言的具体输入（均已成功，问题出在随后的Rust断言）：

```lit
C_abs(3+4*i)=5
log(1/2,(1/2)^(-3))=-3
eval sqrt(0.36)
eval sqrt(2)
```

其中sqrt(0.36)返回精确3/5，旧测试只接受Number(0.6)；sqrt(2)返回精确符号根，旧测试要求EvaluationFailed。

### T05：Point 参数负例与结构集合表示的合同不一致

- 分类：测试期望与数学carrier语义待核对；主标签：`trust`；最早边界：carrier contract。
- 观察：旧负例期待Point<N,R>不能作为Point<Z,R>实参，却被接受。K不出现在字段类型里，tuple表示可能使两实例表示同一集合；不同对象value的错误等式仍拒绝。
- 下一步：明确幻影参数是否应区分carrier，再判断负例该修还是接口该修；当前没有证据宣布放过了错误的数值等式。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：template-wrong-carrier**

```lit
# Showcase migration regression: verified without trust.
# Run: target/release/litex -strict -f examples/wd/template_unique_from_typed_carrier.lit
# Recover S from the already matched t : Point<S> when using a theorem.
struct Point<K nonempty_set, S nonempty_set>:
    value S
    tag N

thm unique_value:
    ? forall K nonempty_set, S nonempty_set, t &Point<K, S>:
        exist! x S st {x = t.value}
    witness exist! x S st {x = t.value} from t.value

template<K nonempty_set, S nonempty_set, t &Point<K, S>>:
    have fn selected_value by exist!:
        ? forall index N:
            exist! x S st {x = t.value}

thm selected_value_spec:
    ? forall K nonempty_set, S nonempty_set, t &Point<K, S>:
        \selected_value<K, S, t>(0) = t.value

struct Unary<S nonempty_set>:
    call fn(x S) S
    tag N

# The template occurs under another call, whose WD uses read-only premises.
thm selected_value_nested:
    ? forall K nonempty_set, S nonempty_set, t &Point<K, S>, op &Unary<S>:
        op.call(\selected_value<K, S, t>(0)) $in S

thm bad:
    ? forall t &Point<N,R>:
        \selected_value<Z,R,t>(0)=t.value
```

实际结果：`success=true`，exit `0`。

**实际输入：phantom-struct-carrier**

```lit
struct Point<K nonempty_set,S nonempty_set>:
    value S
    tag N
forall t &Point<N,R>:
    t $in &Point<Z,R>
```

实际结果：`success=true`，exit `0`。

对照：template-other-instance: 拒绝。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### W01：CLI -e 吞掉以负号开头的合法源码

- 分类：行为问题，根因暂定；主标签：`kernel_problem`；最早边界：launch arguments。
- 观察：-e "-2 < 0" 退出2、无JSON，被当作参数错误；相同源码 -f 和 (-2)<0 的 -e 通过。
- 下一步：检查-e参数消费规则，保留未知flag/缺文件的负例。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

**实际输入：eval-code-starting-with-minus**

```lit
-2 < 0
```

实际结果：`success=none`，exit `2`。

对照：minus-file: 通过；minus-parens: 通过。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

### W02：predeploy 的 Cargo filter 可0测试假绿

- 分类：测试工具覆盖问题；主标签：`trust`；最早边界：test collection。
- 观察：cargo test --release --offline run_examples_only 退出0，但实际执行0个测试；脚本run_cargo_test仅按返回码判success。
- 下一步：确认真正的收集器与库存计数，缺少/零选择应失败；本次未跑发布，也没修脚本。
- 诊断：只确认以下输入的结果；未据此认定缺少整个数学能力或确定共用根因。

```python
GATES = (("docs", "run_docs_markdown_files"),
         ("examples", "run_examples_only"),
         ("showcases", "run_showcases"))
# run_cargo_test: returncode == 0 -> success
```

实际命令：`cargo test --release --offline run_examples_only`；exit0，所有target均running 0 tests。

执行类别：诊断中，未修复。本项验收须保持原数学目标，并检查相关负例；共享表示/状态/搜索或尚未确定语义的修改须进入既有讨论边界。

## Obj 独立失败全集（11项，不是11个独立根因）

全部从实际固定源码文件新提取，旧八个简写失败已归为历史探针。

### fn_set-P04

拥有者：`examples/test_objs/fn_set.lit`。

```lit
sketch:
    let F = fn(x R) x
    $is_set(F)
```

`success=false`；exit `1`；完整失败输出见纠正receipt。

### sum-P107

拥有者：`examples/test_objs/sum.lit`。

```lit
sketch:
    have n N+
    have c R
    have f,g fn(k Z) R
    sum(1,n,fn(k Z) R {c}) = n*c
    sum(1,n,fn(k Z) R {f(k)+g(k)}) = sum(1,n,f)+sum(1,n,g)
    sum(1,n,fn(k Z) R {f(k)-g(k)}) = sum(1,n,f)-sum(1,n,g)
    sum(1,n,fn(k Z) R {c*f(k)}) = c*sum(1,n,f)
```

`success=false`；exit `1`；完整失败输出见纠正receipt。

### sum-P108

拥有者：`examples/test_objs/sum.lit`。

```lit
sketch:
    have n N+
    have f fn(k Z) R
    sum(1,n+1,f) = sum(1,n,f)+sum(n+1,n+1,f)
    sum(1,n,fn(k Z) Z {k+k}) = sum(1,n,fn(j Z) Z {2*j})
```

`success=false`；exit `1`；完整失败输出见纠正receipt。

### product-P103

拥有者：`examples/test_objs/product.lit`。

```lit
sketch:
    have n N+
    have c R*
    have f fn(k Z) R
    product(1,n,fn(k Z) R* {c}) = c^n
    product(1,n+1,f) = product(1,n,f)*product(n+1,n+1,f)
```

`success=false`；exit `1`；完整失败输出见纠正receipt。

### sum_of_finite_set-P103

拥有者：`examples/test_objs/sum_of_finite_set.lit`。

```lit
sketch:
    have S finite_set
    have c R
    have f,g fn(k S) R
    finite_set_sum(S,fn(k S) R {c}) = finite_set_size(S)*c
    finite_set_sum(S,fn(k S) R {f(k)+g(k)}) = finite_set_sum(S,f)+finite_set_sum(S,g)
    finite_set_sum(S,fn(k S) R {f(k)-g(k)}) = finite_set_sum(S,f)-finite_set_sum(S,g)
    finite_set_sum(S,fn(k S) R {c*f(k)}) = c*finite_set_sum(S,f)
```

`success=false`；exit `1`；完整失败输出见纠正receipt。

### sum_of_finite_set-P106

拥有者：`examples/test_objs/sum_of_finite_set.lit`。

```lit
sketch:
    algo flag(x R) R by cases:
        case x = 0: 0
        case x != 0: 1
    finite_set_sum({1/3,2/3},flag) = 2
```

`success=false`；exit `1`；完整失败输出见纠正receipt。

### product_of_finite_set-P103

拥有者：`examples/test_objs/product_of_finite_set.lit`。

```lit
sketch:
    have S finite_set
    have c R*
    have f,g fn(k S) R
    finite_set_product(S,fn(k S) R* {c}) = c^finite_set_size(S)
    finite_set_product(S,fn(k S) R {f(k)*g(k)}) = finite_set_product(S,f)*finite_set_product(S,g)
```

`success=false`；exit `1`；完整失败输出见纠正receipt。

### finite_set_reduce-P02

拥有者：`examples/test_objs/finite_set_reduce.lit`。

```lit
sketch:
    finite_set_reduce({2}, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 0) = 2
```

`success=false`；exit `1`；完整失败输出见纠正receipt。

### finite_set_reduce-P03

拥有者：`examples/test_objs/finite_set_reduce.lit`。

```lit
sketch:
    finite_set_reduce({1, 2}, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 0) = 3
```

`success=false`；exit `1`；完整失败输出见纠正receipt。

### finite_set_reduce-P04

拥有者：`examples/test_objs/finite_set_reduce.lit`。

```lit
sketch:
    finite_set_reduce({2, 1}, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 0) = 3
```

`success=false`；exit `1`；完整失败输出见纠正receipt。

### finite_set_reduce-P05

拥有者：`examples/test_objs/finite_set_reduce.lit`。

```lit
sketch:
    finite_set_reduce({1, 2}, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 10) = 13
```

`success=false`；exit `1`；完整失败输出见纠正receipt。

## 旧输入复查全集与剩余边界

以下记录保留已被显式证明替换的原代码。“拒绝”不能直接升级为内核bug。模块上下文丢失、保留字C命名冲突、严格模式拒绝trust和真正的阴性在分类列明确列出。

### historical-old-gap_gaps_anonymous_fn__p06.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: anonymous_fn P06
let y = 3
fn(x R) R {x + y}(2) = 5
```

首个结果：`{"success": false, "statement": "fn (x R) R{x + y}(2) = 5", "why_failed": {"phase": "search_proof", "goal": "fn (x R) R{x + y}(2) = 5"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_arccot__p02.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: arccot P02
arccot(1) = pi / 4
```

首个结果：`{"success": false, "statement": "arccot(1) = pi / 4", "why_failed": {"phase": "search_proof", "goal": "arccot(1) = pi / 4"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_arccot__p04.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: arccot P04
arccot(-1) = 3 * pi / 4
```

首个结果：`{"success": false, "statement": "arccot(-1) = 3 * pi / 4", "why_failed": {"phase": "search_proof", "goal": "arccot(-1) = 3 * pi / 4"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_arctan__p02.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: arctan P02
arctan(1) = pi / 4
```

首个结果：`{"success": false, "statement": "arctan(1) = pi / 4", "why_failed": {"phase": "search_proof", "goal": "arctan(1) = pi / 4"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_arctan__p03.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: arctan P03
arctan(-1) = -pi / 4
```

首个结果：`{"success": false, "statement": "arctan(-1) = -pi / 4", "why_failed": {"phase": "search_proof", "goal": "arctan(-1) = -pi / 4"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_cart__p04.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: cart P04
cart({1}, {2}) = {(1, 2)}
```

首个结果：`{"success": false, "statement": "cart({1}, {2}) = {(1, 2)}", "why_failed": {"phase": "search_proof", "goal": "cart({1}, {2}) = {(1, 2)}"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_cart_dim__p04.lit

分类：C与builtin复数集冲突；Product别名对照通过。实际结果：`success=false`。

```lit
# Intended valid regression: cart_dim P04
let C = cart(R, Z)
cart_dim(C) = 2
```

首个结果：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "ProductShape", "failure": {"phase": "CartDim", "failure": {"phase": "requirement", "obj": "cart_dim(C)", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "$is_cart(C)", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}}}}}}}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_closed_range__p04.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: closed_range P04
closed_range(-1, 1) = {-1, 0, 1}
```

首个结果：`{"success": false, "statement": "closed_range(-1, 1) = {-1, 0, 1}", "why_failed": {"phase": "search_proof", "goal": "closed_range(-1, 1) = {-1, 0, 1}"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_complex_abs__p03.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_complex_abs__p04.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_complex_abs__p05.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_complex_abs__p06.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_cos__p04.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_cot__p02.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_cot__p03.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_family_intersect__p01.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: family_intersect P01
family_intersect({{1}}) = {1}
```

首个结果：`{"success": false, "statement": "family_intersect({{1}}) = {1}", "why_failed": {"phase": "search_proof", "goal": "family_intersect({{1}}) = {1}"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_family_intersect__p02.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: family_intersect P02
family_intersect({{1, 2}, {2, 3}}) = {2}
```

首个结果：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "SetOperator", "failure": {"phase": "FamilyIntersect", "failure": {"phase": "child", "obj": "{{1, 2}, {2, 3}}", "failure": {"phase": "SetFormer", "failure": {"phase": "ListSet", "failure": {"phase": "requirement", "obj": "{{1, 2}, {2, 3}}", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{1, 2} != {2, 3}", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{1, 2}", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}, {"type": "by_def", "family"`。

### historical-old-gap_gaps_family_intersect__p03.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: family_intersect P03
family_intersect({{1}, {}}) = {}
```

首个结果：`{"success": false, "statement": "family_intersect({{1}, {}}) = {}", "why_failed": {"phase": "search_proof", "goal": "family_intersect({{1}, {}}) = {}"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_family_intersect__p04.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: family_intersect P04
let I = family_intersect({{1}, {2}})
I = I
```

首个结果：`{"success": false, "statement": "let …", "why_failed": {"type": "define_obj", "rule_name": "Let binding", "message": "Bind a name to a well-defined value", "phase": "let", "failure": {"success": false, "obj": "family_intersect({{1}, {2}})", "phase": "well_defined", "failure": {"phase": "SetOperator", "failure": {"phase": "FamilyIntersect", "failure": {"phase": "child", "obj": "{{1}, {2}}", "failure": {"phase": "SetFormer", "failure": {"phase": "ListSet", "failure": {"phase": "requirement", "obj": "{{1}, {2}}", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{1} != {2}", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{1}", "child_obj_well_defined": [{"type": "by_def", "`。

### historical-old-gap_gaps_family_union__p02.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_family_union__p03.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: family_union P03
family_union({{1}, {2}}) = {1, 2}
```

首个结果：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "SetOperator", "failure": {"phase": "FamilyUnion", "failure": {"phase": "child", "obj": "{{1}, {2}}", "failure": {"phase": "SetFormer", "failure": {"phase": "ListSet", "failure": {"phase": "requirement", "obj": "{{1}, {2}}", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{1} != {2}", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{1}", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}], "requirement_fact_verified": []}, {"type": "by_def"`。

### historical-old-gap_gaps_family_union__p04.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: family_union P04
1 $in family_union({{1}, {2}})
```

首个结果：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "atomic_except_equality", "success": false, "phase": "well_defined", "failure": {"phase": "SetOperator", "failure": {"phase": "FamilyUnion", "failure": {"phase": "child", "obj": "{{1}, {2}}", "failure": {"phase": "SetFormer", "failure": {"phase": "ListSet", "failure": {"phase": "requirement", "obj": "{{1}, {2}}", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{1} != {2}", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{1}", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}], "requirement_fact_verified": []}, {"t`。

### historical-old-gap_gaps_family_union__p05.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: family_union P05
let U = family_union({{}, {1, 2}})
U = {1, 2}
```

首个结果：`{"success": false, "statement": "U = {1, 2}", "why_failed": {"phase": "search_proof", "goal": "U = {1, 2}"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_field_access__p01.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_finite_seq_set__p05.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: finite_seq_set P05
fn(x closed_range(1, 2)) R {x} $in finite_seq(R, 2)
```

首个结果：`{"success": false, "statement": "fn (x closed_range(1, 2)) R{x} $in finite_seq(R, 2)", "why_failed": {"phase": "search_proof", "goal": "fn (x closed_range(1, 2)) R{x} $in finite_seq(R, 2)"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_finite_set_max__p04.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_finite_set_min__p04.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_finite_set_size__p05.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: finite_set_size P05
finite_set_size({{1}, {2}}) = 2
```

首个结果：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "FiniteSetStat", "failure": {"phase": "FiniteSetSize", "failure": {"phase": "child", "obj": "{{1}, {2}}", "failure": {"phase": "SetFormer", "failure": {"phase": "ListSet", "failure": {"phase": "requirement", "obj": "{{1}, {2}}", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{1} != {2}", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{1}", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}], "requirement_fact_verified": []}, {"type": "by_`。

### historical-old-gap_gaps_fn_obj__p05.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: fn_obj P05
have fn f(x R) R = x + 1
f(f(1)) = 3
```

首个结果：`{"success": false, "statement": "f(f(1)) = 3", "why_failed": {"phase": "search_proof", "goal": "f(f(1)) = 3"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_fn_obj__p06.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: fn_obj P06
have fn f(x R) fn(y R) R = fn(y R) R {x + y}
f(2)(3) = 5
```

首个结果：`{"success": false, "statement": "f(2)(3) = 5", "why_failed": {"phase": "search_proof", "goal": "f(2)(3) = 5"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_fn_range__p02.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: fn_range P02
fn_range(fn(x R) R {x}) = R
```

首个结果：`{"success": false, "statement": "fn_range(fn (x R) R{x}) = R", "why_failed": {"phase": "search_proof", "goal": "fn_range(fn (x R) R{x}) = R"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_identifier_with_export_file_id__p04_main.lit

分类：缺少历史模块上下文；不计作内核复现。实际结果：`success=false`。

```lit
# Intended valid regression: identifier_with_export_file_id P04
have k R = 1
tuple_dim(base::pair) = 2
```

首个结果：`"Runtime(ParseError(RuntimeParseError { message: \"unknown export `base` in the current module's litex.config\", line: 3, path: Eval }))"`。

### historical-old-gap_gaps_identifier_with_export_file_id__p05_main.lit

分类：缺少历史模块上下文；不计作内核复现。实际结果：`success=false`。

```lit
# Intended valid regression: identifier_with_export_file_id P05
have k R = 1
tuple_dim(other::pair) = 3
```

首个结果：`"Runtime(ParseError(RuntimeParseError { message: \"unknown export `other` in the current module's litex.config\", line: 3, path: Eval }))"`。

### historical-old-gap_gaps_identifier_with_mod_and_export_file_id__p04_main.lit

分类：缺少历史模块上下文；不计作内核复现。实际结果：`success=false`。

```lit
# Intended valid regression: identifier_with_mod_and_export_file_id P04
have k R = 1
tuple_dim(Values::base::pair) = 2
```

首个结果：`"Runtime(ParseError(RuntimeParseError { message: \"unknown import alias `Values` in the current module\", line: 3, path: Eval }))"`。

### historical-old-gap_gaps_identifier_with_mod_and_export_file_id__p05_main.lit

分类：缺少历史模块上下文；不计作内核复现。实际结果：`success=false`。

```lit
# Intended valid regression: identifier_with_mod_and_export_file_id P05
have k R = 1
tuple_dim(Values::other::pair) = 3
```

首个结果：`"Runtime(ParseError(RuntimeParseError { message: \"unknown import alias `Values` in the current module\", line: 3, path: Eval }))"`。

### historical-old-gap_gaps_imaginary_part__p04.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_index_intersect__p02.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: index_intersect P02
have fn A(k {1}) power_set(N) = {k}
index_intersect({1}, N, A) = {1}
```

首个结果：`{"success": false, "statement": "have fn …", "why_failed": {"type": "define_fn", "rule_name": "Have function equal", "message": "Define a named function equal to an anonymous function", "phase": "have_fn_equal", "failure": {"success": false, "obj": "fn (k {1}) power_set(N){{k}}", "phase": "well_defined", "failure": {"phase": "FunctionSpace", "failure": {"phase": "AnonymousFn", "failure": {"phase": "body_in_return_set", "failure": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{k} $in power_set(N)", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{k}", "child_obj_well_defined": [{"type": "by_def", "family": "Identifier", "kind": "Identifier", "obj": "k"}], "requirement_fact_verif`。

### historical-old-gap_gaps_index_union__p02.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: index_union P02
have fn A(k {1}) power_set(N) = {k}
index_union({1}, N, A) = {1}
```

首个结果：`{"success": false, "statement": "have fn …", "why_failed": {"type": "define_fn", "rule_name": "Have function equal", "message": "Define a named function equal to an anonymous function", "phase": "have_fn_equal", "failure": {"success": false, "obj": "fn (k {1}) power_set(N){{k}}", "phase": "well_defined", "failure": {"phase": "FunctionSpace", "failure": {"phase": "AnonymousFn", "failure": {"phase": "body_in_return_set", "failure": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{k} $in power_set(N)", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{k}", "child_obj_well_defined": [{"type": "by_def", "family": "Identifier", "kind": "Identifier", "obj": "k"}], "requirement_fact_verif`。

### historical-old-gap_gaps_intersect__p01.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: intersect P01
intersect({1, 2}, {2, 3}) = {2}
```

首个结果：`{"success": false, "statement": "intersect({1, 2}, {2, 3}) = {2}", "why_failed": {"phase": "search_proof", "goal": "intersect({1, 2}, {2, 3}) = {2}"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_list_set__p04.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: list_set P04
{1, 2} = {2, 1}
```

首个结果：`{"success": false, "statement": "{1, 2} = {2, 1}", "why_failed": {"phase": "search_proof", "goal": "{1, 2} = {2, 1}"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_list_set__p06.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: list_set P06
{1} $in {{1}, {2}}
```

首个结果：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "atomic_except_equality", "success": false, "phase": "well_defined", "failure": {"phase": "SetFormer", "failure": {"phase": "ListSet", "failure": {"phase": "requirement", "obj": "{{1}, {2}}", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{1} != {2}", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{1}", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}], "requirement_fact_verified": []}, {"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{2}", "child_obj_well_defined": [{"type": "by_def", "fami`。

### historical-old-gap_gaps_list_set__p07.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: list_set P07
(1, 2) $in {(1, 2), (2, 1)}
```

首个结果：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "atomic_except_equality", "success": false, "phase": "well_defined", "failure": {"phase": "SetFormer", "failure": {"phase": "ListSet", "failure": {"phase": "requirement", "obj": "{(1, 2), (2, 1)}", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "(1, 2) != (2, 1)", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "ProductShape", "kind": "Tuple", "obj": "(1, 2)", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}, {"type": "by_def", "family": "Literal", "kind": "Number", "obj": "2"}], "requirement_fact_verified": []}, {"type": "by_def", "family": "ProductSh`。

### historical-old-gap_gaps_log__p05.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_log__p06.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: log P06
log(e, e) = 1
```

首个结果：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "ExpLogOperator", "failure": {"phase": "Log", "failure": {"phase": "requirement", "obj": "log (e, e)", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "e != 1", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Literal", "kind": "EulerNumber", "obj": "e"}, {"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}}}}}}}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_max__p05.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_min__p05.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_obj_at_index__p04.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: obj_at_index P04
((1, 2), 3)[1][2] = 2
```

首个结果：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "ProductShape", "failure": {"phase": "ObjAtIndex", "failure": {"phase": "requirement", "obj": "((1, 2), 3)[1][2]", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "$is_tuple(((1, 2), 3)[1])", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "ProductShape", "kind": "ObjAtIndex", "obj": "((1, 2), 3)[1]", "obj_well_defined": {"type": "by_def", "family": "ProductShape", "kind": "Tuple", "obj": "((1, 2), 3)", "child_obj_well_defined": [{"type": "by_def", "family": "ProductShape", "kind": "Tuple", "obj": "(1, 2)", "child_obj_well_de`。

### historical-old-gap_gaps_obj_at_index__p06.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: obj_at_index P06
(2 + 3, 4 * 2)[2] = 8
```

首个结果：`{"success": false, "statement": "(2 + 3, 4 * 2)[2] = 8", "why_failed": {"phase": "search_proof", "goal": "(2 + 3, 4 * 2)[2] = 8"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_pow__p04.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_power_set__p06.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: power_set P06
power_set(power_set({})) = {{}, {{}}}
```

首个结果：`{"success": false, "statement": "power_set(power_set({})) = {{}, {{}}}", "why_failed": {"phase": "search_proof", "goal": "power_set(power_set({})) = {{}, {{}}}"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_range__p04.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: range P04
range(-2, 1) = {-2, -1, 0}
```

首个结果：`{"success": false, "statement": "range(-2, 1) = {-2, -1, 0}", "why_failed": {"phase": "search_proof", "goal": "range(-2, 1) = {-2, -1, 0}"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_range__p06.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: range P06
not 3 $in range(1, 3)
```

首个结果：`{"success": false, "statement": "not 3 $in range(1, 3)", "why_failed": {"phase": "search_proof", "goal": "not 3 $in range(1, 3)"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_real_part__p04.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_real_part__p06.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_seq_set__p03.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: seq_set P03
fn(x N+) N {x} $in seq(N)
```

首个结果：`{"success": false, "statement": "fn (x N+) N{x} $in seq(N)", "why_failed": {"phase": "search_proof", "goal": "fn (x N+) N{x} $in seq(N)"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_seq_set__p04.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: seq_set P04
fn(x N+) R {0} $in seq(R)
```

首个结果：`{"success": false, "statement": "fn (x N+) R{0} $in seq(R)", "why_failed": {"phase": "search_proof", "goal": "fn (x N+) R{0} $in seq(R)"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_set_minus__p01.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: set_minus P01
set_minus({1, 2}, {2}) = {1}
```

首个结果：`{"success": false, "statement": "set_minus({1, 2}, {2}) = {1}", "why_failed": {"phase": "search_proof", "goal": "set_minus({1, 2}, {2}) = {1}"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_sin__p04.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_standard_set_r_pos__p03.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_struct_obj__p01.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_struct_obj__p02.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_tan__p02.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_tan__p03.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_tan__p04.lit

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### historical-old-gap_gaps_tuple__p04.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: tuple P04
((1, 2), 3)[1][2] = 2
```

首个结果：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "ProductShape", "failure": {"phase": "ObjAtIndex", "failure": {"phase": "requirement", "obj": "((1, 2), 3)[1][2]", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "$is_tuple(((1, 2), 3)[1])", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "ProductShape", "kind": "ObjAtIndex", "obj": "((1, 2), 3)[1]", "obj_well_defined": {"type": "by_def", "family": "ProductShape", "kind": "Tuple", "obj": "((1, 2), 3)", "child_obj_well_defined": [{"type": "by_def", "family": "ProductShape", "kind": "Tuple", "obj": "(1, 2)", "child_obj_well_de`。

### historical-old-gap_gaps_tuple__p06.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: tuple P06
(1, 2) != (2, 1)
```

首个结果：`{"success": false, "statement": "(1, 2) != (2, 1)", "why_failed": {"phase": "search_proof", "goal": "(1, 2) != (2, 1)"}, "stores": [], "infers": []}`。

### historical-old-gap_gaps_union__p01.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Intended valid regression: union P01
union({1}, {2}) = {1, 2}
```

首个结果：`{"success": false, "statement": "union({1}, {2}) = {1, 2}", "why_failed": {"phase": "search_proof", "goal": "union({1}, {2}) = {1, 2}"}, "stores": [], "infers": []}`。

### named-K005

分类：已登记的自动否定存在式边界；显式反证路线通过。实际结果：`success=false`。

```lit
forall x {0}:
    x != 1
not exist x {0} st {x = 1}
```

首个结果：`{"success": false, "statement": "not exist x {0} st {x = 1}", "why_failed": {"phase": "search_proof", "goal": "not exist x {0} st {x = 1}"}, "stores": [], "infers": []}`。

### named-anonymous_bad_application

分类：阴性/能力边界控制；不计作正例bug。实际结果：`success=false`。

```lit
fn(x R) N {x}(-1) = -1
```

首个结果：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "FnObj", "failure": {"phase": "child", "obj": "fn (x R) N{x}", "failure": {"phase": "FunctionSpace", "failure": {"phase": "AnonymousFn", "failure": {"phase": "body_in_return_set", "failure": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "x $in N", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Identifier", "kind": "Identifier", "obj": "x"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "N"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}}}}}}}}}, "stores": [], "infers": []}`。

### named-anonymous_bad_return

分类：阴性/能力边界控制；不计作正例bug。实际结果：`success=false`。

```lit
let f = fn(x R) N {x}
```

首个结果：`{"success": false, "statement": "let …", "why_failed": {"type": "define_obj", "rule_name": "Let binding", "message": "Bind a name to a well-defined value", "phase": "let", "failure": {"success": false, "obj": "fn (x R) N{x}", "phase": "well_defined", "failure": {"phase": "FunctionSpace", "failure": {"phase": "AnonymousFn", "failure": {"phase": "body_in_return_set", "failure": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "x $in N", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Identifier", "kind": "Identifier", "obj": "x"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "N"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}}}}}}}, "stores": [], "infers": []}`。

### named-bound_builtin

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### named-bound_lower

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### named-cart_alias

分类：C与builtin复数集冲突；Product别名对照通过。实际结果：`success=false`。

```lit
let C = cart(R, Z)
cart_dim(C) = 2
```

首个结果：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "ProductShape", "failure": {"phase": "CartDim", "failure": {"phase": "requirement", "obj": "cart_dim(C)", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "$is_cart(C)", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}}}}}}}, "stores": [], "infers": []}`。

### named-cart_empty

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### named-cart_nested_projection

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### named-decimal_after_addition

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### named-decimal_equal

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### named-decimal_not_equal

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
2.400 != 2.4
```

首个结果：`{"success": false, "statement": "2.4 != 2.4", "why_failed": {"phase": "search_proof", "goal": "2.4 != 2.4"}, "stores": [], "infers": []}`。

### named-display_trust_have

分类：-strict按合同拒绝trust；不是数学/输出回归。实际结果：`success=false`。

```lit
trust have trusted_a R:
    trusted_a = 1
trusted_a = 1
```

首个结果：`"Runtime(InvalidArguments(\"`trust` / `trust have` are forbidden under Litex `-strict`\"))"`。

### named-empty_index_expected_rejection

分类：阴性/能力边界控制；不计作正例bug。实际结果：`success=false`。

```lit
have fn empty_family(empty_index {}) power_set(N) = {}
index_union({}, N, empty_family) = {}
```

首个结果：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "SetOperator", "failure": {"phase": "IndexUnion", "failure": {"phase": "requirement", "obj": "index_union({}, N, empty_family)", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "$is_nonempty_set({})", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{}", "child_obj_well_defined": [], "requirement_fact_verified": []}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}}}}}}}, "stores": [], "infers": []}`。

### named-false_equality_control

分类：阴性/能力边界控制；不计作正例bug。实际结果：`success=false`。

```lit
0 = 1
```

首个结果：`{"success": false, "statement": "0 = 1", "why_failed": {"phase": "search_proof", "goal": "0 = 1"}, "stores": [], "infers": []}`。

### named-false_npos

分类：阴性/能力边界控制；不计作正例bug。实际结果：`success=false`。

```lit
0 $in N+
```

首个结果：`{"success": false, "statement": "0 $in N+", "why_failed": {"phase": "search_proof", "goal": "0 $in N+"}, "stores": [], "infers": []}`。

### named-false_order

分类：阴性/能力边界控制；不计作正例bug。实际结果：`success=false`。

```lit
0 > 0
```

首个结果：`{"success": false, "statement": "0 > 0", "why_failed": {"phase": "search_proof", "goal": "0 > 0"}, "stores": [], "infers": []}`。

### named-family_have_fn

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### named-family_let

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### named-family_literal_membership

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### named-finite_product_wrong_domain

分类：阴性/能力边界控制；不计作正例bug。实际结果：`success=false`。

```lit
let s = finite_set_product({1}, fn(x {2}) Z {x})
```

首个结果：`{"success": false, "statement": "let …", "why_failed": {"type": "define_obj", "rule_name": "Let binding", "message": "Bind a name to a well-defined value", "phase": "let", "failure": {"success": false, "obj": "finite_set_product({1}, fn (x {2}) Z{x})", "phase": "well_defined", "failure": {"phase": "IteratedOperator", "failure": {"phase": "ProductOfFiniteSet", "failure": {"phase": "requirement", "obj": "finite_set_product({1}, fn (x {2}) Z{x})", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{1} $subset {2}", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{1}", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}], "requireme`。

### named-finite_reduce_addition

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### named-finite_reduce_subtraction

分类：阴性/能力边界控制；不计作正例bug。实际结果：`success=false`。

```lit
let r = finite_set_reduce({1, 2}, fn(x Z) Z {x}, fn(a, b Z) Z {a - b}, 0)
```

首个结果：`{"success": false, "statement": "let …", "why_failed": {"type": "define_obj", "rule_name": "Let binding", "message": "Bind a name to a well-defined value", "phase": "let", "failure": {"success": false, "obj": "finite_set_reduce({1, 2}, fn (x Z) Z{x}, fn (a, b Z) Z{a - b}, 0)", "phase": "well_defined", "failure": {"phase": "IteratedOperator", "failure": {"phase": "FiniteSetReduce", "failure": {"phase": "requirement", "obj": "finite_set_reduce({1, 2}, fn (x Z) Z{x}, fn (a, b Z) Z{a - b}, 0)", "result": {"type": "forall", "success": false, "phase": "search_proof", "fact": "forall __param_5, __param_6 Z:\n    fn (a, b Z) Z{a - b}(__param_5, __param_6) = __param_5 - __param_6\n    fn (a, b Z) Z{a - b}(__param_6, __param_5) = __param_6 - __param_5\n    __param_5 - __param_6 = __param_6 - __param`。

### named-finite_sum_closed_value

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### named-finite_sum_eval

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### named-finite_sum_valid_domain

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### named-finite_sum_wrong_domain

分类：阴性/能力边界控制；不计作正例bug。实际结果：`success=false`。

```lit
let s = finite_set_sum({1}, fn(x {2}) Z {x})
```

首个结果：`{"success": false, "statement": "let …", "why_failed": {"type": "define_obj", "rule_name": "Let binding", "message": "Bind a name to a well-defined value", "phase": "let", "failure": {"success": false, "obj": "finite_set_sum({1}, fn (x {2}) Z{x})", "phase": "well_defined", "failure": {"phase": "IteratedOperator", "failure": {"phase": "SumOfFiniteSet", "failure": {"phase": "requirement", "obj": "finite_set_sum({1}, fn (x {2}) Z{x})", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{1} $subset {2}", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{1}", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "1"}], "requirement_fact_veri`。

### named-fold_wrong_domain

分类：阴性/能力边界控制；不计作正例bug。实际结果：`success=false`。

```lit
let bad = finite_set_reduce({0, 1}, fn(x {2}) Z {x}, fn(a, b Z) Z {a + b}, 0)
```

首个结果：`{"success": false, "statement": "let …", "why_failed": {"type": "define_obj", "rule_name": "Let binding", "message": "Bind a name to a well-defined value", "phase": "let", "failure": {"success": false, "obj": "finite_set_reduce({0, 1}, fn (x {2}) Z{x}, fn (a, b Z) Z{a + b}, 0)", "phase": "well_defined", "failure": {"phase": "IteratedOperator", "failure": {"phase": "FiniteSetReduce", "failure": {"phase": "requirement", "obj": "finite_set_reduce({0, 1}, fn (x {2}) Z{x}, fn (a, b Z) Z{a + b}, 0)", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{0, 1} $subset {2}", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{0, 1}", "child_obj_well_defined": [{"type": "by_def", "famil`。

### named-fold_wrong_predicate

分类：阴性/能力边界控制；不计作正例bug。实际结果：`success=false`。

```lit
let bad = finite_set_reduce({0, 1}, fn(x Z: x > 0) Z {x}, fn(a, b Z) Z {a + b}, 0)
```

首个结果：`{"success": false, "statement": "let …", "why_failed": {"type": "define_obj", "rule_name": "Let binding", "message": "Bind a name to a well-defined value", "phase": "let", "failure": {"success": false, "obj": "finite_set_reduce({0, 1}, fn (x Z: x > 0) Z{x}, fn (a, b Z) Z{a + b}, 0)", "phase": "well_defined", "failure": {"phase": "IteratedOperator", "failure": {"phase": "FiniteSetReduce", "failure": {"phase": "requirement", "obj": "finite_set_reduce({0, 1}, fn (x Z: x > 0) Z{x}, fn (a, b Z) Z{a + b}, 0)", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "0 > 0", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "0"}, {"type": "by_def", "family": "Literal", "kind": "Number", "obj`。

### named-guarded_fold_good

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### named-guarded_sum_bad

分类：阴性/能力边界控制；不计作正例bug。实际结果：`success=false`。

```lit
let s = finite_set_sum({0, 1}, fn(x Z: x > 0) Z {x})
```

首个结果：`{"success": false, "statement": "let …", "why_failed": {"type": "define_obj", "rule_name": "Let binding", "message": "Bind a name to a well-defined value", "phase": "let", "failure": {"success": false, "obj": "finite_set_sum({0, 1}, fn (x Z: x > 0) Z{x})", "phase": "well_defined", "failure": {"phase": "IteratedOperator", "failure": {"phase": "SumOfFiniteSet", "failure": {"phase": "requirement", "obj": "finite_set_sum({0, 1}, fn (x Z: x > 0) Z{x})", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "0 > 0", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "0"}, {"type": "by_def", "family": "Literal", "kind": "Number", "obj": "0"}], "predicate_signature": {"type": "builtin"}, "pr`。

### named-i_inverse

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### named-i_nonzero

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### named-max_complex

分类：阴性/能力边界控制；不计作正例bug。实际结果：`success=false`。

```lit
let n = finite_set_max({i})
```

首个结果：`{"success": false, "statement": "let …", "why_failed": {"type": "define_obj", "rule_name": "Let binding", "message": "Bind a name to a well-defined value", "phase": "let", "failure": {"success": false, "obj": "finite_set_max({i})", "phase": "well_defined", "failure": {"phase": "FiniteSetStat", "failure": {"phase": "FiniteSetMax", "failure": {"phase": "requirement", "obj": "finite_set_max({i})", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{i} $subset R", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{i}", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "ImaginaryUnit", "obj": "i"}], "requirement_fact_verified": []}, {"type": "by_def", "fa`。

### named-max_real

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### named-min_complex

分类：阴性/能力边界控制；不计作正例bug。实际结果：`success=false`。

```lit
let n = finite_set_min({i})
```

首个结果：`{"success": false, "statement": "let …", "why_failed": {"type": "define_obj", "rule_name": "Let binding", "message": "Bind a name to a well-defined value", "phase": "let", "failure": {"success": false, "obj": "finite_set_min({i})", "phase": "well_defined", "failure": {"phase": "FiniteSetStat", "failure": {"phase": "FiniteSetMin", "failure": {"phase": "requirement", "obj": "finite_set_min({i})", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{i} $subset R", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{i}", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "ImaginaryUnit", "obj": "i"}], "requirement_fact_verified": []}, {"type": "by_def", "fa`。

### named-nested_addition_associativity

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
forall a, b, c Z:
    fn(x, y Z) Z {x + y}(fn(x, y Z) Z {x + y}(a, b), c) = fn(x, y Z) Z {x + y}(a, fn(x, y Z) Z {x + y}(b, c))
```

首个结果：`{"success": false, "statement": "forall a, b, c Z:\n    fn (x, y Z) Z{x + y}(fn (x, y Z) Z{x + y}(a, b), c) = fn (x, y Z) Z{x + y}(a, fn (x, y Z) Z{x + y}(b, c))", "why_failed": {"phase": "search_proof", "goal": "forall a, b, c Z:\n    fn (x, y Z) Z{x + y}(fn (x, y Z) Z{x + y}(a, b), c) = fn (x, y Z) Z{x + y}(a, fn (x, y Z) Z{x + y}(b, c))"}, "stores": [], "infers": []}`。

### named-pow_log_direct

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
have x N
2^(log(2, 2^x)) = 2^x
```

首个结果：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "ArithmeticOperator", "failure": {"phase": "Pow", "failure": {"phase": "requirement", "obj": "2 ^ log (2, 2 ^ x)", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "log (2, 2 ^ x) $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "ExpLogOperator", "kind": "Log", "obj": "log (2, 2 ^ x)", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "2"}, {"type": "by_def", "family": "ArithmeticOperator", "kind": "Pow", "obj": "2 ^ x", "child_obj_well_defined": [{"type": "by_def", "family": "L`。

### named-pow_log_order_bridge

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
have x N
2^x > 0
2^(log(2, 2^x)) = 2^x
```

首个结果：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "ArithmeticOperator", "failure": {"phase": "Pow", "failure": {"phase": "requirement", "obj": "2 ^ log (2, 2 ^ x)", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "log (2, 2 ^ x) $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "ExpLogOperator", "kind": "Log", "obj": "log (2, 2 ^ x)", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "2"}, {"type": "by_known", "obj": "2 ^ x", "wd_id": "wd3"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fa`。

### named-pow_log_positive_bridge

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
have x N
2^x $in R+
2^(log(2, 2^x)) = 2^x
```

首个结果：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "ArithmeticOperator", "failure": {"phase": "Pow", "failure": {"phase": "requirement", "obj": "2 ^ log (2, 2 ^ x)", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "log (2, 2 ^ x) $in Z", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "ExpLogOperator", "kind": "Log", "obj": "log (2, 2 ^ x)", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "Number", "obj": "2"}, {"type": "by_known", "obj": "2 ^ x", "wd_id": "wd3"}], "requirement_fact_verified": [{"type": "atomic_except_equality", "success": true, "fa`。

### named-single_field_struct

分类：含单字段struct；现行明确限制/例子待迁移。实际结果：`success=false`。

```lit
struct ScalarOps:
    add fn(x, y R) R
```

首个结果：`"Runtime(ParseError(RuntimeParseError { message: \"struct definition expects at least two fields\", line: 1, path: Eval }))"`。

### named-sqrt_nonzero

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### named-true_order

分类：本次原样通过；只能关闭这个直接输入，不能推断整类能力已无问题。实际结果：`success=true`。

### named-weighted_unordered_fold

分类：阴性/能力边界控制；不计作正例bug。实际结果：`success=false`。

```lit
let r = finite_set_reduce({1, 2}, fn(x Z) Z {x}, fn(a, b Z) Z {2*a + b}, 0)
```

首个结果：`{"success": false, "statement": "let …", "why_failed": {"type": "define_obj", "rule_name": "Let binding", "message": "Bind a name to a well-defined value", "phase": "let", "failure": {"success": false, "obj": "finite_set_reduce({1, 2}, fn (x Z) Z{x}, fn (a, b Z) Z{2 * a + b}, 0)", "phase": "well_defined", "failure": {"phase": "IteratedOperator", "failure": {"phase": "FiniteSetReduce", "failure": {"phase": "requirement", "obj": "finite_set_reduce({1, 2}, fn (x Z) Z{x}, fn (a, b Z) Z{2 * a + b}, 0)", "result": {"type": "forall", "success": false, "phase": "search_proof", "fact": "forall __param_5, __param_6 Z:\n    fn (a, b Z) Z{2 * a + b}(__param_5, __param_6) = 2 * __param_5 + __param_6\n    fn (a, b Z) Z{2 * a + b}(__param_6, __param_5) = 2 * __param_6 + __param_5\n    2 * __param_5 + __p`。

### current-file-examples/module_manager/file_prefix/b.lit

分类：阴性/能力边界控制；不计作正例bug。实际结果：`success=false`。

```lit
# Intentionally false. If `-f a.lit` ever runs this file, the project fails.
1 = 2
```

首个结果：`{"success": false, "statement": "1 = 2", "why_failed": {"phase": "search_proof", "goal": "1 = 2"}, "stores": [], "infers": []}`。

### current-file-examples/module_manager/import_alias_qualified_arithmetic/main.lit

分类：原数学目标的直接写法；参考上面的具体能力边界/现存显式证明。实际结果：`success=false`。

```lit
# Tracer: persistent dependencies belong to litex.config, not Litex source.
#
# Before:
# import "../../_internal/fixtures/geometry_foundation" as gf
# Former behavior: an isolated .lit file could mutate the module graph while statements executed.
#
# Now: the adjacent litex.config owns the gf dependency, so this source contains only Litex
# statements and qualified mathematical references.

gf::main::a + gf::main::a = gf::main2::b
gf::main::pair[1] = 3
gf::main2::pair[1] = 8
cart_dim(gf::main::ProductSet) = 2

# Current behavior: project execution discovers gf before parsing this file. An interactive REPL may
# issue the same import as a terminal command, which mutates only its ephemeral in-memory manifest.
#
# Boundary: uncommenting the old import line is rejected in every .lit source, including
# `litex -isolated -f`; unknown qualified names such as gf::main::missing remain rejected.
```

首个结果：`{"success": false, "statement": "<wd_failed>", "why_failed": {"phase": "well_defined", "verification": {"type": "equality", "success": false, "phase": "well_defined", "failure": {"phase": "ArithmeticOperator", "failure": {"phase": "Add", "failure": {"phase": "requirement", "obj": "m0::f0::a + m0::f0::a", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "m0::f0::a $in C", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "Identifier", "kind": "Identifier", "obj": "m0::f0::a"}, {"type": "by_def", "family": "StandardSet", "kind": "StandardSet", "obj": "C"}], "predicate_signature": {"type": "builtin"}, "predicate_domain": []}}}}}}}, "stores": [], "infers": []}`。

### current-file-examples/stmt_nodes/definition/let_template_struct_aliases.lit

分类：含单字段struct；现行明确限制/例子待迁移。实际结果：`success=false`。

```lit
# Stmt: let + template + struct alias composition
# Run: litex -f examples/stmt_nodes/definition/let_template_struct_aliases.lit
#
# `let` composes with `template` at two useful levels. The template below
# returns a parameterized struct, so the example also exposes the carrier
# boundary of a transparent abbreviation.

struct Triple<X set>:
    first X
    second X
    third X

template<X set>:
    have fn triple(a, b, c X) &Triple<X> = (a, b, c)

# Fix the template parameter and retain the ordinary function parameters.
let triple_R = \triple<R>

# Fix the complete application result.
let chosen = \triple<R>(1, 2, 3)

triple_R(4, 5, 6) = (4, 5, 6)
chosen = (1, 2, 3)

# `let` stores a transparent equality but does not create carrier evidence.
# Introduce a typed object only when later mathematics needs struct fields.
have chosen_struct &Triple<R> = chosen
chosen_struct.first = 1

# These remain outside the current field-access boundary because neither let
# name owns a direct struct carrier:
# triple_R(4, 5, 6).first = 4
# chosen.first = 1

# A `let` may also name a callable field reached through a nested struct. The
# verifier derives the retained `(x, y R) -> R` contract from the field-access
# object's frozen `ScalarOps` view; `scalar_add` is still only a transparent
# local abbreviation, not a second function declaration.
struct ScalarOps:
    add fn(x, y R) R

struct Space:
    scalars &ScalarOps

thm callable_struct_field_alias:
    ? forall space &Space, x, y R:
        space.scalars.add(x, y) = space.scalars.add(x, y)
    let scalar_add = space.scalars.add
    scalar_add(x, y) = space.scalars.add(x, y)
```

首个结果：`"Runtime(ParseError(RuntimeParseError { message: \"struct definition expects at least two fields\", line: 39, path: Real(\"/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-04/remaining-issues-audit/snapshot/examples/stmt_nodes/definition/let_template_struct_aliases.lit\") }))"`。

### current-file-examples/test_statements/boundaries/finite-negated-existence-automatic-search.lit

分类：已登记的自动否定存在式边界；显式反证路线通过。实际结果：`success=false`。

```lit
# Current automatic-search limitation; explicit by-contra is the accepted route.
# This boundary deliberately expects search_proof failure on the final assertion.
forall x {0}:
    x != 1
not exist x {0} st {x = 1}
```

首个结果：`{"success": false, "statement": "not exist x {0} st {x = 1}", "why_failed": {"phase": "search_proof", "goal": "not exist x {0} st {x = 1}"}, "stores": [], "infers": []}`。

### current-file-examples/wd_negative/finite_extrema_nonreal.lit

分类：阴性/能力边界控制；不计作正例bug。实际结果：`success=false`。

```lit
# Both finite extrema must reject the reserved imaginary unit.
let bad_max = finite_set_max({i})
let bad_min = finite_set_min({i})
```

首个结果：`{"success": false, "statement": "let …", "why_failed": {"type": "define_obj", "rule_name": "Let binding", "message": "Bind a name to a well-defined value", "phase": "let", "failure": {"success": false, "obj": "finite_set_max({i})", "phase": "well_defined", "failure": {"phase": "FiniteSetStat", "failure": {"phase": "FiniteSetMax", "failure": {"phase": "requirement", "obj": "finite_set_max({i})", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{i} $subset R", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{i}", "child_obj_well_defined": [{"type": "by_def", "family": "Literal", "kind": "ImaginaryUnit", "obj": "i"}], "requirement_fact_verified": []}, {"type": "by_def", "fa`。

### current-file-examples/wd_negative/finite_set_fold_domain.lit

分类：阴性/能力边界控制；不计作正例bug。实际结果：`success=false`。

```lit
# Invalid finite fold iterands: neither the domain nor its predicate covers the set.
let bad_domain = finite_set_reduce({0, 1}, fn(x {2}) Z {x}, fn(a, b Z) Z {a + b}, 0)
let bad_predicate = finite_set_reduce({0, 1}, fn(x Z: x > 0) Z {x}, fn(a, b Z) Z {a + b}, 0)
```

首个结果：`{"success": false, "statement": "let …", "why_failed": {"type": "define_obj", "rule_name": "Let binding", "message": "Bind a name to a well-defined value", "phase": "let", "failure": {"success": false, "obj": "finite_set_reduce({0, 1}, fn (x {2}) Z{x}, fn (a, b Z) Z{a + b}, 0)", "phase": "well_defined", "failure": {"phase": "IteratedOperator", "failure": {"phase": "FiniteSetReduce", "failure": {"phase": "requirement", "obj": "finite_set_reduce({0, 1}, fn (x {2}) Z{x}, fn (a, b Z) Z{a + b}, 0)", "result": {"type": "atomic_except_equality", "success": false, "phase": "search_proof", "fact": "{0, 1} $subset {2}", "well_defined": {"well_defined_of_each_parameter": [{"type": "by_def", "family": "SetFormer", "kind": "ListSet", "obj": "{0, 1}", "child_obj_well_defined": [{"type": "by_def", "famil`。

## Rust 失败全集

完整Cargo输出/断言行号/源代码均在receipt。下面保持精确测试名。6项旧输出/表示断言不应当作数学目标失败；Point幻影参数那项需先确定carrier合同。

- `execute::exact_numeric_periodic_modulus::logarithm_algebra_for_positive_nonunit_bases` — 旧输出/表示/路线断言。
- `execute::exact_numeric_periodic_modulus::new_leaves_inherit_search_ceiling_and_do_not_store_search_facts` — 旧输出/表示/路线断言。
- `execute::exact_numeric_periodic_modulus::new_rule_normal_output_is_bilingual` — 旧输出/表示/路线断言。
- `execute::exec_stmt_transaction_tests::not_in_and_set_algebra_builtin_rules` — 实际证明/前提消费失败；具体源与首个失败在receipt，尚未证明共用根因。
- `execute::exec_stmt_transaction_tests::rational_sum_of_two_fractions_with_product_denominator` — 实际证明/前提消费失败；具体源与首个失败在receipt，尚未证明共用根因。
- `execute::exec_stmt_transaction_tests::template_have_fn_by_induc_object_definition_unfold` — 实际证明/前提消费失败；具体源与首个失败在receipt，尚未证明共用根因。
- `execute::execute_eval_stmt::exec_eval_stmt_tests::aggregate_algorithm_terms_keep_checked_equations_and_eval_stores_empty` — 实际证明/前提消费失败；具体源与首个失败在receipt，尚未证明共用根因。
- `execute::execute_eval_stmt::exec_eval_stmt_tests::eval_factorial_sqrt_log_closed_numeric_succeed` — 旧输出/表示/路线断言。
- `execute::execute_eval_stmt::exec_eval_stmt_tests::eval_non_square_sqrt_soft_fails` — 旧输出/表示/路线断言。
- `execute::execute_fact_stmt::verify_atomic_fact::verify_equality::showcase_local_rules_tests::cosine_integer_offset_positive_and_evidence` — 实际证明/前提消费失败；具体源与首个失败在receipt，尚未证明共用根因。
- `execute::execute_fact_stmt::verify_atomic_fact::verify_equality::showcase_local_rules_tests::full_add2_chain_and_projection_boundaries` — 实际证明/前提消费失败；具体源与首个失败在receipt，尚未证明共用根因。
- `execute::finite_set_cardinality_rule_tests::finite_set_cardinality_rule_detailed_retains_winning_route_and_premises` — 实际证明/前提消费失败；具体源与首个失败在receipt，尚未证明共用根因。
- `execute::finite_set_cardinality_rule_tests::finite_set_cardinality_rule_finiteness_order_alias_and_candidate_fallback` — 实际证明/前提消费失败；具体源与首个失败在receipt，尚未证明共用根因。
- `execute::finite_set_cardinality_rule_tests::finite_set_cardinality_rule_normal_explains_actual_certificates_in_both_languages` — 实际证明/前提消费失败；具体源与首个失败在receipt，尚未证明共用根因。
- `execute::finite_set_cardinality_rule_tests::finite_set_cardinality_rule_symbolic_composition` — 实际证明/前提消费失败；具体源与首个失败在receipt，尚未证明共用根因。
- `execute::induction_repair_tests::induction_examples_cover_the_maintained_acceptance_sources` — 实际证明/前提消费失败；具体源与首个失败在receipt，尚未证明共用根因。
- `execute::induction_repair_tests::induction_goal_wd_uses_the_induction_domain_without_ih` — 实际证明/前提消费失败；具体源与首个失败在receipt，尚未证明共用根因。
- `execute::legacy_next_capabilities::builtin_permission_and_depth_are_inherited` — 实际证明/前提消费失败；具体源与首个失败在receipt，尚未证明共用根因。
- `execute::legacy_next_capabilities::finite_product_fresh_insertion` — 实际证明/前提消费失败；具体源与首个失败在receipt，尚未证明共用根因。
- `execute::legacy_next_capabilities::normal_bilingual_contract` — 实际证明/前提消费失败；具体源与首个失败在receipt，尚未证明共用根因。
- `execute::legacy_next_capabilities::ordered_reduce_partition` — 实际证明/前提消费失败；具体源与首个失败在receipt，尚未证明共用根因。
- `execute::legacy_small_capability_repair_tests::legacy_small_unordered_fold_laws` — 实际证明/前提消费失败；具体源与首个失败在receipt，尚未证明共用根因。
- `execute::order_stage_a_remainder_tests::order_stage_a_finite_set_size_union_and_surjection` — 实际证明/前提消费失败；具体源与首个失败在receipt，尚未证明共用根因。
- `execute::showcase_local_repair_tests::declared_field_types_close_nested_calls_without_releasing_laws` — 旧输出/表示/路线断言。
- `execute::showcase_local_repair_tests::original_showcase_sections_use_the_repaired_paths` — 实际证明/前提消费失败；具体源与首个失败在receipt，尚未证明共用根因。
- `execute::showcase_local_repair_tests::unique_function_templates_recover_hidden_carriers_and_work_in_nested_wd` — Point幻影参数负例合同待核对。

## 已恢复与有意保留的限制

以下本次通过，不能继续沿用旧失败状态：

```lit
2.400 = 2.4
i != 0
1/i = -1*i
sum(1,3,fn(x Z) Z{x}) = 6
product(1,4,fn(x Z) Z{x}) = 24
exp(ln(2)) = 2
(27/8)^(2/3) = 9/4
```

上下确界builtin release、choice定义消费、合法有限fold对象的WD、前驱单独证明、tuple模板别名typed值及语句集成检查也有本次通过记录。它们与未通过的等式/嵌套组合分别记录。

- 已明确保留：单字段struct；缺证明前提的负例；错误域、非实 extrema、非AC减法fold；自动否定存在式边界。
- 用户此前不要求实现：超大幂溢出后强算、庞大模幂展开、一般无理根比较和根式分母能力；本轮没有把这些扩展列为新bug。
- 新的Point负例被接受不自动意味着不健全；其K未参与字段carrier，另外不同对象value的错误等式拒绝。

## 重放与证据边界

从receipt取出`verified/source-frozen.zip`到独立目录，`cargo build --release --offline`，再运行：

```sh
cargo test --release --offline --lib -- --nocapture
cargo test --release --offline --test test_statements -- --nocapture
python3 examples/test_objs/run.py
python3 examples/test_statements/run.py --binary target/release/litex
```

独立输入用`target/release/litex -strict -e <完整代码>`；以负号开头的代码必须保留该参数门禁本身，普通证明可用-f重放。基础runner的manifest、输入、session、module/cold-cache记录在receipt。`eval`展示结果，不等同于将等式存为事实。

- 构建成功且固定副本源码在各门禁前后稳定。发布前根工作区相对该副本仍有并行变化；不把它冒充本报告已检验版本。
- 未执行全部公开example/docs/showcase/教材/发布/Lean门禁；这些范围不作全绿承诺。
- 一个早期缓存测试程序的源码对应关系没有独立确认，已排除最终统计。最终Rust统计来自固定副本内实际新执行的Cargo。
- 审计脚本复跑覆盖过部分早期门禁报告；已用固定副本重新完整构建并执行上述全部门禁，以最终fresh receipts为依据。保留的早期记录只用于解释版本变化。
