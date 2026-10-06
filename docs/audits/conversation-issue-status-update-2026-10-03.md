# Conversation issue status update — 2026-10-03

> Historical audit: these code fences preserve dated verifier observations,
> including rejected inputs and excerpts that depend on their original context.
> They are evidence, not current standalone tutorial examples. The maintained
> executable language examples are in the Manual, README, and examples corpus.

> Follow-up migration checkpoint: bounds certificate signatures, mapping
> definition publication, checked surjective/choice proofs and the concrete
> surjection-size example have newer evidence in
> [builtin migration audit](builtin-prop-thm-migration-2026-10-03.md).
> The template alias chain and single-field struct restriction remain open;
> use the newer audit's explicit source/binary checkpoint for current status.

本次重新构建并执行后的结论：**没有全部解决；部分修复仍有效，同时出现新的回归。**
本次只复查和更新记录，没有修改 Rust、数学例子、公开配置或技能。
旧检查点见 [上一次完整复查](conversation-issue-recheck-2026-10-03.md)。

## 可复现版本与检查范围

`cargo build --release` 成功；固定源码在构建前后与复制后一致。
固定程序与例子/std 副本进行检查；源码与程序指纹记录在
[完整 journal](../../examples/test_statements/proof_journals/conversation_issue_status_update_2026-10-03.json)。

| 检查 | 本次结果 |
| --- | --- |
| 当前 Obj 正例文件 | 81/99 通过；16 普通拒绝，2 InternalBug；594 个正例 ID 是库存数量，不是全部通过的断言数 |
| 当前 Obj 阴性文件 | 289/289 正确拒绝，无 InternalBug/崩溃 |
| 当前已登记直接 gap | 22/22 仍拒绝 |
| 上次未通过的 67 个原样直接输入 | 24 通过，43 仍拒绝；独立保留已删除/改写 fixture 的旧源码 |
| 当前 Stmt 回归 | 356/377 符合预期，21 项失败；不是 21 个独立根因 |
| 虚数反证，同源串行新进程 | 6/12 通过，6/12 拒绝，仍不稳定 |
| 之前失败的 37 个公开文件 | 23 通过，14 未通过 |

比起上次 67 个直接输入全部拒绝，24 个已有恢复；但当前库存中的多个
显式正例也失败，不能用 gap 数量下降来声称整个系统已通过。
没有重跑整库 Rust、教材、Lean、发布/打包门禁。

## 仍有效的修复与可用证明路径

<!-- litex:skip-test -->
```litex
0 > 0                         # 正常拒绝，无栈溢出
1 > 0                         # 通过
2^(-3) = 1/8                  # 通过
sin(-pi/2) = -1               # 通过
C_abs(3+4*i) = 5              # 通过
finite_set_max({1/3,1/2}) = 1/2 # 通过
```

`finite_set_max({i})` / `finite_set_min({i})`、非法函数域、错误的无序减法
fold 仍拒绝。负例通过只证明这些边界，没有证明所有合法 aggregate 可用。
简单 struct 字段旧输入 `p.x=1`、`p.second=2` 恢复；模板/别名整链仍未恢复。
K005 的现存显式枚举/反证文件在副本和真实工作区都通过。

幂对数原文件仍失败，但相同数学目标的以下显式证明仍通过，无额外假设或 trust：

<!-- litex:skip-test -->
```litex
have x N
log(2, 2^x) = x
2^(log(2, 2^x)) = 2^x
```

限定名原文件仍失败，加入以下定义释放后完整文件通过，无 trust：

<!-- litex:skip-test -->
```litex
release obj def gf::main::a
release obj def gf::main2::b
release obj def gf::main::pair
release obj def gf::main2::pair
release obj def gf::main::ProductSet
gf::main::a + gf::main::a = gf::main2::b
```

以上两项归为已验证的 Litex authoring / example migration 路径，原公开调用文件
尚未迁移，不能说原样文件已修好。`let Product=cart(R,Z); cart_dim(Product)=2`
也通过；旧探针 `let C=...` 与原生 C 名称冲突，不以它证明一般 cart 别名缺陷。

## 旧问题仍未关闭

### 反证结果不稳定

<!-- litex:skip-test -->
```litex
by contra:
    ? i != 0
    i * i = -1
    impossible i * i != 0
```

同一固定版本串行 12 次，6 次通过、6 次在 by_contra 拒绝。
直接 `i!=0` 通过，错误的 `i=0` 拒绝。属于实现行为不稳定，机制仍未定位；
不能仅凭数次通过关闭，也不能猜测是哈希遍历或全局深度的问题。

### 上下确界谓词注册/接线

<!-- litex:skip-test -->
```litex
release thm real_least_upper_bound_exists({0}, 1)
release thm real_greatest_lower_bound_exists({0}, 0)
```

生成结论的 WD 仍报 `undefined_predicate`，缺少
`is_real_least_upper_bound` / `is_real_greatest_lower_bound`。六个原公开文件仍失败。
最早边界是注册/结论 WD；不能先把下游定理逐个补写。

### choice 与满射的定义证明组合

<!-- litex:skip-test -->
```litex
have fn g_choice(alpha {1}) power_set({1}) = {1}
have fn f_choice(alpha {1}) {1} = 1
forall alpha {1}:
    f_choice(alpha) $in g_choice(alpha)
by def $is_choice_function_for({1}, power_set({1}), g_choice, f_choice)
```

点态成员事实通过，by def 仍拒绝。choice axiom release 已通过不代表此 consumer 已修复。
原接口仍是 g:I->S 与 f:I->family_union(S)。

<!-- litex:skip-test -->
```litex
have A set = {1, 2}
have B set = {1}
have fn f(x A) B = 1
exist x A st {x = 1}
by def $surjective(A, B, f)
```

满射大小原文件此次更早在存在式 `exist x A st {x=1}` 拒绝。
保留新的首个失败点，不沿用“只在 cardinality/by def 失败”的旧定位。
两项暂归 definition/callable/搜索证据组合，根因和修复 owner 待定位。

### struct 别名与模板调用整链

<!-- litex:skip-test -->
```litex
let chosen = \triple<R>(1, 2, 3)
chosen = (1, 2, 3)
have chosen_struct &Triple<R> = chosen
chosen_struct.first = 1
```

原文件现在更早在 `chosen=(1,2,3)` 的调用签名 WD 失败；typed struct 声明通过，
字段等式仍失败。简单直接字段恢复不足以关闭模板/别名组合问题。

## 本次确认的回归

### 合法无序加法 fold 被拒绝

<!-- litex:skip-test -->
```litex
let r = finite_set_reduce({1,2}, fn(x Z) Z{x}, fn(a,b Z) Z{a+b}, 0)
```

原样输入上次通过，现在在 WD 的展开/结合律证明要求拒绝。
专用正例 `examples/wd/finite_set_fold_domain.lit` 在真实工作区也失败，
其非法域/减法阴性仍正确拒绝。属于已确认行为回归，不能认为仅补上 AC 检查即完全修复。

### 递归与归纳的域/载体证明回归

<!-- litex:skip-test -->
```litex
have fn ind_count(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: ind_count(n - 1)
```

当前在递归分支的参数 WD 拒绝；`by induc` / `by strong_induc` 还在 `k+1 in R`
等载体要求失败。21 个 Stmt 回归失败集中在递归函数、递归 algo、模板中的递归、
普通/强归纳、递归 eval 及显式递归边界。真实工作区的 have_fn/by_induc 文件重跑同样失败。
只报告已定位的失败要求，尚不认定为同一个全局搜索原因。

### Aggregate 推理内部错误

`examples/test_objs/sum.lit` 与 `product.lit` 产生
`InternalBug("inferred fact 0 < #11#j failed well-definedness check")`。
这是 runtime/storage-inference operational failure，不是普通数学拒绝。
`fn_set.lit` 另有 `undefined name x` 解析失败；仍需核对新作用域规则和 fixture 意图。

`sqrt_quotient.lit` 的 `a/b in R+`、函数 family 的模块例子也比上一检查点失败。
所有完整源码与首个失败输出已保留在 journal；本次没有擅自修改搜索权限、AST 或状态结构。

## 尚未通过的 owning Obj 文件

| 文件 | 首个失败源码/输出 |
| --- | --- |
| [anonymous_fn.lit](../../examples/test_objs/anonymous_fn.lit) | `fn (x R) R{x + y}(2) = 2 + y = 2 + 3 = 5` |
| [closed_range.lit](../../examples/test_objs/closed_range.lit) | `closed_range(3, 1) = {}` |
| [exp.lit](../../examples/test_objs/exp.lit) | `forall x R:     exp(x) > 0` |
| [finite_set_reduce.lit](../../examples/test_objs/finite_set_reduce.lit) | `<wd_failed>` |
| [fn_obj.lit](../../examples/test_objs/fn_obj.lit) | `f(2)(3) = fn (y R) R{2 + y}(3) = 2 + 3 = 5` |
| [fn_range.lit](../../examples/test_objs/fn_range.lit) | `by extension` |
| [fn_set.lit](../../examples/test_objs/fn_set.lit) | `Runtime(ParseError(RuntimeParseError { message: "undefined name `x`", line: 22, path: Real("examples/test_objs/fn_set.lit") }))` |
| [instantiated_template_obj.lit](../../examples/test_objs/instantiated_template_obj.lit) | `<wd_failed>` |
| [intersect.lit](../../examples/test_objs/intersect.lit) | `not 1 $in intersect({1, 2}, {2, 3})` |
| [product.lit](../../examples/test_objs/product.lit) | `Runtime(InternalBug("inferred fact 0 < #11#j failed well-definedness check"))` |
| [product_of_finite_set.lit](../../examples/test_objs/product_of_finite_set.lit) | `finite_set_product(S, fn (k S) R*{c}) = c ^ finite_set_size(S)` |
| [range.lit](../../examples/test_objs/range.lit) | `range(2, 2) = {}` |
| [reduce.lit](../../examples/test_objs/reduce.lit) | `reduce(2, 2, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 0) = 2` |
| [set_builder.lit](../../examples/test_objs/set_builder.lit) | `let …` |
| [set_minus.lit](../../examples/test_objs/set_minus.lit) | `not 2 $in set_minus({1, 2}, {2})` |
| [sum.lit](../../examples/test_objs/sum.lit) | `Runtime(InternalBug("inferred fact 0 < #11#j failed well-definedness check"))` |
| [sum_of_finite_set.lit](../../examples/test_objs/sum_of_finite_set.lit) | `finite_set_sum(S, fn (k S) R{c}) = finite_set_size(S) * c` |
| [union.lit](../../examples/test_objs/union.lit) | `by extension` |

22 个当前直接 gap 和所有 Stmt 失败的逐项源码/要求见完整 journal。它们不是独立 bug 计数。

本次较早检查点反证 8/12 通过；工作区更新后重新构建、重跑全套，最新检查点为上述结果。两版回放都保留在 journal，未混用程序。

源码 SHA-256: `c33784ee2fb188f6ef6b9184e2dfd116fde19602120887ea082a071fe0ece785`；程序 SHA-256: `ffc4c6e637cad241473d26e6670bbf647c4e35db627ed75d801dd424e878d84c`。

最终稳定性复核：`{'snapshot_source_stable': True, 'fixed_binary_stable': True, 'workspace_source_still_matches': True, 'workspace_binary_still_matches': True}`。
