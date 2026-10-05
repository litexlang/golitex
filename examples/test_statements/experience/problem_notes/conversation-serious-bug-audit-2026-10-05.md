# 对话收尾：严重 bug 复核 — 2026-10-05

任务：用户要求一次性汇报具体严重 bug，局部修复直接完成，不重复提出模糊语义问题。
本轮检查当前 Rust / CLI / exec / WD / 作用域与严格模式；不把证明步骤不足、
未接入的数学功能或历史观察当成新的严重 bug。验收等级为 L4 审计，实际实施仅局部 parser 修复。

**结果：两处已确认解析缺陷已修；五处旧测试的保留名用法已迁移。此次检查没有发现仍未处理的
假命题接受、strict trust 绕过、崩溃或作用域泄漏。完整 Rust 门仍有一个已有的 DEC04 断言失败，
不能宣称 release 全绿。** 这不是所有数学例子、所有 builtin 分支或独立 proof replay 的完整验收。

## LEG30：声明了保留对象名，引用却读 builtin — 已解决

旧代码实际接受：

```litex
have fn picked(e R)R=e
picked(2)=e
```

这里 body 是 EulerNumber；声明的参数 Identifier 没有被引用。改目标为
`picked(2)=2` 反而失败。类似问题也出现在声明 C 后 body 仍读取复数集合。
这不能被夸大成“任意实数为正 / 任意集合非空都被证明”。

现有 `define_plain_atom_as_parse` wrapper 增加纯保留名检查，拒绝 object-primary
在 Identifier lookup 前就消费的名字；在分配 Identifier 前返回普通 ParseError。
没有调整 AST、lookup 优先级、命名状态或 Runtime 字段。正确写法：

```litex
have fn picked(t R)R=t
picked(2)=2
```

稳定 tracer：[reserved_object_bindings.lit](../../../wd/reserved_object_bindings.lit)。
[四项真实 Runtime 回归](../../../../tests/unit/parse/reserved_object_bindings.rs)
覆盖 eval / REPL / root export、20 个保留名、函数/量词/函数集/匿名函数/set builder/
template/struct/field/prop/theorem/witness/preimage/induction 入口，以及失败后名字复用、
原生 builtin 和相似普通名称。Normal / Detailed 也观察实际结果。

完整门发现五处原有测试使用这些 builtin 名字，全部只改 authored name，保留断言：

- 自定义 `sign` 函数改 `signum`，相同 cases 和 reflexivity 目标；
- 正偶数变量 `i` 改 `count`，相同整数/正性/余数前提及 `1<count`；
- dependent-have 的 `C` 改 `D`，相同 dependent carrier 与数值结论；
- index-cart 的函数参数 `i` 改 `index`，相同 choice 条件和结论；
- literal-beta 负例的任意集合参数 `Z` 改 `W`，仍须普通 WD/proof 拒绝，
  不能用 parse 错误替代负例的原检查。

迁移前完整门 928/934、6 失败；迁移后 933/934，仅 DEC04 失败。
原输入、逐文件 before/after/hash 和全部失败输出在验收回执包，未删除或放宽负断言。

## LEG27：模块限定 struct 类型在 :: 处解析失败 — 已解决

在真实配置的 Lib 导出 facts 中定义：

```litex
struct Pair:
    first R
    second R
```

主文件原代码：

```litex
have item &Lib::facts::Pair=(1,2)
item.first=item.first
```

原 parser 只消费一个 simple name，随后在 `::` 失败。现在 struct-view 复用已有
`parse_prop_name` 的完整 AtomicName owner/export 解析，与 template 同一入口。
原两行不改目标就通过；没有丢弃 qualifier、重定义 AST 或改 import/view 状态。

[稳定配置与入口](../../../module_manager/qualified_struct_views/README.md)检查同名的
R/Z/N 三个真实 owner、current-export、完整 import、单 export `:::`、generic 参数、
function return 和 nested field carrier。[四项实际 launcher 回归](../../../../tests/unit/run_module/qualified_struct_views.rs)
拒绝错误 carrier、字段值、字段名、参数数量/非空条件、未知 module/export/struct、
不合法路径及多 export 的 flattened spelling。完整路径在多 export 下仍成功。

附带尝试的 `nested.point.first=1/2` 在 qualified 和 plain 控制都只是 search miss；
声明的 nested field type 验证通过。`release struct def` 也没有自动补成这个具体值等式。
本轮没有修改该自动改写能力，更没有把 field membership 正例冒充 value equality 通过。
原探索和必要的显式 struct-member 前提保存在 raw 中。

## 唯一未通过的已有 Rust 断言：DEC04

```litex
struct Point<K nonempty_set,S nonempty_set>:
    value S
    tag N
forall t &Point<N,R>:
    t $in &Point<Z,R>
```

K 没有出现在字段中，两实例按现行 tuple 定义都描述 R × N；已有显式 extension
控制也能证明这两个集合相同。旧 template 测试却要求对应应用拒绝。
本轮没有找到由此导致错误数值等式或 trust 绕过的证据，也没有擅改 struct 表示、
把 K 塞进字段或删除旧 negative。它保持在
[所属 folder 的边界记录](../../bugs/def_struct_stmt/limitations.md)，本轮不再重复发起语义提问。

## 本次验收与边界

同一最终 production CLI 的 SHA256 是
`dddc1902feee4bbdfd163994ed84aef4867ea447041184f680d1d24b87f55b8d`。
最终完整 Rust lib **933 通过 / 1 失败 / 934**，integration **1/1**；命令 exit 101。
Stmt **378/378、50 leaves、0 gaps**；基础 **175/175**；Obj **99 个正文件 / 666 assertions**
及 **309 个负文件**均符合预期；额外实际 CLI 正负控制 **49/49**；五个稳定文件和一个
真实模块入口通过，另两个迁移后的原 fixture 通过。正负判断同时核验 JSON 与 exit。

strict 直接及传递暖缓存错误定理拒绝、有效缓存控制仍过；已修的 C 平方和反例、
除零、缺 carrier/guard、错误 OR 分支、错误 witness、scope/rollback 和复合反证控制
在此次全 Rust / 基础 / 专项门里保持。先前 FN07/GEO03 原稳定 tracer 也通过。

本轮未重新跑完整数学 showcase、geo、教材、Lean、所有文档 collector 或独立证据 replay。
已知规则缺口、长例 proof/超时与发布 collector 债保留原清单；不把它们算成新的严重系统 bug，
也不因本次基础语义门通过而宣称这些范围已完成。其它 session 的源码工作均保留。

[全部命令、数量、源码漂移和未成功尝试](../../../../tests/tooling/acceptance/conversation-serious-bug-audit-2026-10-05.md)。
