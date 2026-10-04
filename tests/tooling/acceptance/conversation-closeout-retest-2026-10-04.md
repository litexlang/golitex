# 对话收尾复测 — 2026-10-04

Task: 用户要求重新测试本对话提出的问题，直接完成有确定合同的局部修复，只把不能代维护者决定的事项留下。Scope: Rust targets、Stmt、基础语义/CLI、tooling、实际阶段例子、正式文档和所选模块/showcase。共同工作区仍在开发，本页只说明各冻结截面的实测结果。

**本轮审计已完成；完整上线门没有通过。最高优先级的确认缺陷是 strict 从非 strict 缓存接受 `0 = 1`。提议的 strict 冷验 guard 尚未应用，具体缓存授权待答。** 不把未决语义断言、超时或审计里的历史失败改成绿例。

机器回执：[JSON](conversation-closeout-retest-2026-10-04.json)。原始日志、输入、逐例结果、源码指纹、冻结二进制和未应用 patch：[证据包](conversation-closeout-retest-2026-10-04_receipts.zip)。旧失败/错误尝试也在包内；这不是完整 proof replay 或 Lean 验收。

## 实测范围

| 门/集合 | 实际选择与结果 | 边界 |
| --- | --- | --- |
| Rust lib | 最后稳定截面 820 项：817 pass / 3 fail（exit 101） | 原 induction/phantom 正负期望及新 strict-cache 拒绝断言保留 |
| Rust integration | 1/1 pass | bin target 的 0 tests 不算额外覆盖 |
| Stmt | 50 AST leaves，378/378 checks，0 mismatch，0 gap | 包含规定的负例与能力边界；不是全部 kernel 分支 |
| 基础语义/功能 | 175/175 | 正负、WD、作用域/回滚、strict、入口、JSON/exit |
| Tooling | 18/18 | 当前 Run 消费、计数、取消/超时及错误一致性 |
| 阶段例子 | 871 selected / completed / matched；0 unclassified | proof_nodes、stmt_nodes、wd、infer、tokenize、knowledge_base 和三个 negative 目录 |
| Markdown | 453 fences：225/225 正式片段通过；audit 228 中 117 pass / 111 fail | 总 collector exit 1；111 全在 docs/audits，含历史反例、缺上下文及真实能力缺口 |

阶段扫描只有文件自己声明不完整覆盖的 `def_algo_mismatch.lit` 按负例处理；没有把其它失败正例改为负例。此次专用阶段 runner 有非零计数和失败 exit，不替代未恢复的生产全量 collector。

更广的旧截面观察：1037 个输入中模块项 43 无数学预期；126 个 showcase 4 pass、17 fail、105 次 30 秒 timeout。复查 21 个已完成 showcase 为 4 pass / 17 fail；105 超时没有重新全部跑完，也不等于 105 个确认 bug。与已有 SH/GEO/LEG 卡去重，不从这组观察推断全量正确。完整 textbook gate 未执行。

最后 CLI 范围使用冻结二进制 SHA256 `f3cbf7bb1f765d2cd1d960efa5b50d7e7d2acd989138389278331ed35463a0cf`。Rust 与各 collector 的 command、退出值、实际计数、耗时、source_before/source_after 和漂移另列，不将不同截面相加。初轮及部分重编译有其他会话漂移；最终Rust和CLI各门回执自身均无运行中漂移；末尾文档复查的audit比前次多两个失败，正是相同的已知短版squared-i输入，前次119/109与末次117/111原样保留。来源 fingerprint 是排序路径→SHA256 映射的 JSON SHA256，原始映射在证据包中。

## 已直接完成的工作

作者路线补了原目标所需的显式递归等式、数值消元、有限性/子集、callback 签名、归纳类型和定义展开桥。精确数值及 Detailed 消费者现核对实际证据/FactId；原错值、缺非零、权限、seed、freshness、作用域和 WD 拒绝保留。`{1,1}` 的 distinct-elements 负例保留。其他会话的 eval、JSON/语言和 infer 变更不归因于本轮。

`predeploy_gate.py` 已用当前 `-f` Run envelope，检查 JSON/exit、statement_results 和 session_error，保留取消、超时和空测试拒绝。四个模块挂载入口已保留真实硬错误；普通事实失败仍是 FailToImport。geometry 的 `internal_bug: Litex internal bug: … failed well-definedness check` 经 `-f` 和 `-r` 均可见。这项修复只解决错误被隐藏的问题。

[已解决经验](../../../examples/test_statements/experience/problem_notes/conversation_retest_local_repairs_2026-10-04.md)。所选 Rust tested topology prefix 已通过；整个文件后续 callback beta 的既有失败仍开放。

## 需要维护者决定的六项

<a id="cache"></a>

### 1. P0：strict 缓存策略（LEG29）

依赖：

```litex
thm false_theorem:
    ? 0 = 1
    trust 0 = 1
```

根文件：

```litex
release thm Dep::main::false_theorem
0 = 1
```

冷 strict exit 1；普通运行 exit 0 生成依赖缓存；暖 strict **exit 0 / success true**。源代码未变，缓存缺少 strict 证明来源。新 Rust safety regression 确实选中并失败，没有 ignore 或改变最后的拒绝断言。

建议：`src/run_module/import_kb.rs::try_finish_import_from_kb` 在 strict 下直接返回既有 `ImportKbHit::Miss`，让既有冷验路径执行。没有 AST/Runtime 字段、cache format 或合并/回滚改型；strict 导入更慢。确切未应用 patch 见[提议](conversation-closeout-retest-2026-10-04.proposed-strict-cache.patch.txt)。另一选择是先设计模式/版本/传递依赖完整认证的缓存；一个局部 strict 布尔标记不足以代替该合同。

待决定：批准 strict 冷验 guard，或选择先设计认证缓存。缓存行为受现有 skill 的具体授权门保护，不能因只有数行代码而自行越过。验收：同一源码冷/暖 strict 均拒绝假的 theorem；普通有效导入、直接/传递依赖、strict trust 错误和非 strict 缓存控制保留。

[对应模块及复现命令](../../../examples/module_manager/strict_cache_policy/README.md)；[LEG29](../../../plan/src收尾总清单.md#leg29)。缓存授权问题已异步发出，尚无回复。

<a id="induction"></a>

### 2. 归纳类型证据自动化边界（OBJ10）

```litex
have fn f(x N) N = x
by induc n from 0:
    ? f(n) = f(n)
```

当前 step WD 不能证明 `n + 1 $in N`。同一 goal 后补检查 `n $in N`，普通/强归纳均通过；`from -1` 和从零证明 `n/n=1` 仍拒绝。原自动 positive Rust test 保持 red。

待决定：接受显式 checked 类型事实，或要求归纳自动推导并带证据提供 carrier。建议自动 carrier 作为独立局部功能设计，不全局放宽 Direct 搜索。涉及 shared WD/evidence 合同，不能只删断言。验收包含 bare/explicit ordinary/strong 和错误起点/零除/无 IH 前提控制。

[对应 Stmt 记录](../../../examples/test_statements/bugs/by_induc_stmt/limitations.md)。

<a id="phantom"></a>

### 3. struct 幻影参数的身份（DEC04）

```litex
struct Point<K nonempty_set,S nonempty_set>:
    value S
    tag N
forall t &Point<N,R>:
    t $in &Point<Z,R>
```

当前通过，K 未参与字段；旧 wrong-carrier negative 因而失败。实际字段使用 K 时错误 carrier 拒绝；错误对象值与缺 template guard 也拒绝。未证出错误数值等式，不能直接叫不健全。

待决定：carrier 采用字段集合语义（这里相同），还是所有泛型参数都有名义身份（这里不同）。前者维护旧 expectation；后者修改共享 struct carrier 合同并补表示/打印/JSON/WD/模板消费控制。原 wrong-carrier 断言尚未改。

[对应 struct 记录](../../../examples/test_statements/bugs/def_struct_stmt/limitations.md)；[DEC04](../../../plan/src收尾总清单.md#dec04)。

<a id="contra"></a>

### 4. by contra 的嵌套量词分类表示（DEC01）

```litex
by contra:
    ? forall x {0}:
        exist y {0} st {y = x}
    impossible 0 = 0
```

在构造相反假设时拒绝 `negation_unsupported`；NotForall / PlainExistFact 的 QF-only 载荷无法存 ∃x∀y(y≠x)。QF forall、复合 impossible 及既有十个 Fact 分类已验；失败发生在反假设表示，不是关闭事实类型不支持。同名 binder 导致的另一次 parser 失败已保留但不归因于内核。

待决定：保留明确 unsupported 边界，或先批准一个能承载嵌套量词的具体分类 AST/证据方案；后者需要字段逐项提案和 scope/WD/JSON/replay/Boolean 展开成本控制。统一 NotFact 仍被排除。

[对应记录](../../../examples/test_statements/bugs/by_contra_stmt/limitations.md)；[DEC01](../../../plan/src收尾总清单.md#dec01)。

<a id="qualified"></a>

### 5. 跨文件函数签名与证据 owner（LEG29 / GEO）

原 `problem_927` 的 translation 通过，solution 在 infer 派生等式 WD 报 InternalBug；把同一 translation+solution 拼成一文件（仅去除 `geo::` 限定）通过。公有 Runtime 诊断在已完成 geo export 后绑定 `a,b,c,d cart(R,R)`，下列 reflexivity 已首先失败：

```litex
geo::distance_sq(a,b) = geo::distance_sq(a,b)
```

原因是 FnObj WD “no matching function signature”。`verify_obj/core.rs::collect_in_function_set_candidates` 只扫 live stack，下一步 `fact_by_id_in_stack` 同样只查 live；签名在 finished export。添加一个 candidate 还不能解决证据引用。cache definitions 也可能没有对应 signature FactId。

建议：允许 WD 按 qualified owner 查询已经验证的导出签名，并明确冷验和 cache 声明签名的证据路径；不复制/合并整套 Env，不放宽搜索等级。待决定的是跨导出签名/citation 合同及 cache 缺证据时的处理，然后才能给出局部实现。验收必须覆盖 same-file/cross-file、alias/错 module、arity/carrier/guard、cold/warm、实际 FactId 来源和 InternalBug 停机控制。

[原 source及对应记录](../../../showcases/math_concepts_in_litex/15_coordinate_geometry_case_study/problem_927/issues.md)；原始 Detailed、geometry-wd-trace.rs/JSON 与 same-file 控制在证据包。这里只确认这一 owner 链，未声称所有 geometry 失败同因。

<a id="release"></a>

### 6. 完整发布库存与审计片段预期（REL02 / REL04）

```sh
cargo test --release run_docs_markdown_files
cargo test --release run_examples_only
cargo test --release run_showcases
```

旧 collectors 已移入 memorial，active filters 不代表 corpus。零选择 guard 已保证不会假绿；当前正式 docs 与阶段扫描不能替代完整库存。Audit fences 混有 deliberate negatives、缺上下文和不支持的 true goals，不能统一 expected=false 或批量 skip。

待决定：用逐输入 manifest 明确入口/上下文/预期，还是正式规范分 gate、历史 audit 单独结构化观察；两者都保留全部 inventory、实际数量、失败原因和 timeout。建议沿现有显式 manifest 模式登记，不替换成缩小的 smoke gate。选定后迁移生产 collectors 并执行完整发布/教材门。

[REL02](../../../plan/src收尾总清单.md#rel02)；[REL04](../../../plan/src收尾总清单.md#rel04)。已修的是 file output consumer，不需要恢复被移除的 graph CLI。

## 记录可信度及复查

所有 capture 使用 release/offline isolated target；迭代 proof session 输入/输出在证据包。当前 CLI 没有 skill 历史的 `-compact/-before/-runner/-isolated/try`，故使用当前 `-session` 协议和独立隔离候选，不伪造旧协议验收，也未插入新 trust 去清除本轮目标失败。

`strict-cache-regression` 那次短名称配 `--exact` 实际选中 0 tests，是无效尝试。随后完整限定名选中 1 个并失败，完整 all-targets 也选中该回归。末轮 Rust 首次重编译曾遇另一会话引入但随后修正的 `serde_json` 未声明依赖，保留失败构建，不为此添加依赖或覆盖那一会话的改动。

代码继续变动时，按原 command 在新 release binary 上复查；旧 hash 的 green 只属于其快照。此次没有修改受保护 AST/Env/Runtime 字段，也没有应用受保护缓存提案。执行 ledger 完成后交接至本页及对应 source-owned 决策记录。
