# F 类中可以直接补证明步骤的例子（2026-10-03）

这轮把 23 个 Obj gap 改成有步骤的严格正例，另把 4 个已经恢复的加法 fold 原样搬入正例。
没有修改 Rust、放宽 WD、扩大搜索预算、新增 trust 或弱化数学结论。
`cart_dim` 有一项属于旧 fixture 命名错误：`C` 被解析为复数集合，改用 `product_space`。
因此它保留的是“乘积集合别名的维数”这个测试目的，不能说旧源码中的 builtin `C` 已有维数 2。

主 tracer 在 [union.lit](../../union.lit) 的 P01：

```litex
# 原来直接写 union({1}, {2}) = {1, 2}，search_proof 拒绝。
by extension union({1}, {2}) = {1, 2}
```

原目标是集合相等，现有外延证明接口已经足够。并非每个集合等式都能用这条短写法：
`intersect` 和 `set_minus` 还需要按成员属于 1 或 2 分情况，排除不合法的一支。
完整代码在对应正例 P01；原直断言和每条失败尝试在 journal 中保留。

## 几种可复用的写法

**先证明内层值，再消费外层调用。**

```litex
have fn f(x R) R = x + 1
f(1) = 2
f(f(1)) = f(2) = 3
```

删去 `f(1)=2` 后再次失败，所以这条中间事实有实际作用。
curried 函数先写返回的匿名函数，再将调用结果与函数体连起来：

```litex
have fn f(x R) fn(y R) R = fn(y R) R {x + y}
f(2) = fn(y R) R {2 + y}
f(2)(3) = fn(y R) R {2 + y}(3) = 2 + 3 = 5
```

**先证明选中的 tuple，再做下一层访问。**

```litex
((1, 2), 3)[1] = (1, 2)
((1, 2), 3)[1][2] = 2
```

同样的第一步也让 `eval ((1, 2), 3)[1][2]` 成功；`eval` 仍只展示，不发布等式。
最初额外写了 `$is_tuple` 和 `tuple_dim`，删除两条后仍成功，所以正式用例不保留它们。
错误的外层或内层 index 仍拒绝，错误结果 1 也拒绝。

**把结构字段与对应位置连成一条 equality 链。**

```litex
struct Point:
    x R
    y R
have p &Point = (1, 2)
p.x = p[1] = 1
p.y = p[2] = 2
```

保留 typed 构造，没有给 struct 增加字段或任意桥接公理。错误 `p.x=p[1]=2` 拒绝。
旧 authoring cheatsheet 提到的 `by struct def p` 在这个二进制上仍报
`by: struct is not wired yet`；本次没有恢复该接口。

**构造外层 list-set 之前先证明元素互异。**

```litex
by contra:
    ? {1} != {2}
    1 $in {1}
    1 $in {2}
    impossible 1 $in {2}
{1} $in {{1}, {2}}
```

这是满足原有 list-set WD，不是删掉互异条件。tuple 的互异性用第一位置上的
`1=(1,2)[1]=(2,1)[1]=2` 与 `impossible 1=2`。

**复坐标先展开内层算术。**

```litex
re(-2 - i) = re(-2) - re(i) = -2 - 0 = -2
img(-2 - i) = img(-2) - img(i) = 0 - 1 = -1
i * i = -1
re(i * i) = re(-1) = -1
```

**正集合 membership 先给出严格正性。**

```litex
sqrt(2) > 0
sqrt(2) $in R+
```

只写 `2>0` 然后要求根号的 R+ membership 仍失败；额外 `2>0` 对上面成功版本没有作用，已删去。

## 本次关闭的具体 ID

| 路线 | Obj ID |
| --- | --- |
| 外延与成员证明 | union-P01、intersect-P01、set_minus-P01、list_set-P04、family_union-P02、fn_range-P02 |
| 元素互异 / tuple 反证 | list_set-P06/P07、tuple-P06 |
| 两层索引 / 算术投影 | tuple-P04、obj_at_index-P04/P06 |
| beta 展开与中间调用 | fn_obj-P05/P06、anonymous_fn-P06 |
| 字段到位置 equality | struct_obj-P01/P02、field_access-P01 |
| 复坐标 | real_part-P04/P06、imaginary_part-P04 |
| 正性 | standard_set_r_pos-P03 |
| fixture 别名 | cart_dim-P04 |
| 原样已恢复，不归为本轮 kernel 实现 | finite_set_reduce-P02/P03/P04/P05；N01 移出 gap，原负例保留 |

`fn_range` 的成功证明使用完整定义的 identity 函数，并明确消费
`identity(y)=y`、`identity(y) in fn_range(identity)` 与两个像集合相等；没有 opaque 壳。
`family_union` 显式取得属于 singleton family 的集合，再搬运成员关系。
这些证明已进入所属正例文件，每个 Pxx 仍在独立、丢弃的 `sketch:` 作用域中。

B10 的旧 alpha fixture 也改用了现成的具名 theorem：

```litex
by thm alpha_theorem(1) => $alpha_conclusion(fn(i1 R) R {i1 + 1})
```

整文件普通模式通过；自动发现同一个 forall 的路径仍在原始输入中失败。
它原有 4 条 `trust` 和抽象谓词都保留，strict 会正确拒绝这种背景。
这个结果是旧测试接口迁移，不是把无根据的谓词蕴含证明出来。

## 尝试后仍留下的具体边界

| 问题 | 已经尝试的路线与首个未完成目标 | 下一步 |
| --- | --- | --- |
| family_intersect singleton | 短外延、双向成员证明、两方向分开，仍不能消费 `forall x family_intersect({{1}}): x in {1}` | 查已有集合族成员量化接口；没有证据据此宣布整个语义有错 |
| C_abs 负值和 3+4i | abs 转换、乘法分解、取负重写失败；平方为 25 可证，`C_abs(3+4*i)>=0` 仍失败 | 先补合法非负性/主根消费，不能任取正根 |
| 分数 extrema | `finite_set_max(S) in S` 就失败；eval 的显示结果不能当证明 | 缩小 extrema 的成员接口与分数次序叶 |
| B06 前驱索引 | 原 property 展开、命名 `remainder=set_minus(s,{a})` 都未完成 `obtain prev`；FnSet WD 已过 | 跟踪前驱存在证书的实例化/消费，而不是继续加非空假设 |
| index_union / index_intersect singleton | 短外延仍失败；不放宽 family 函数 WD | 下一轮补带 fiber/witness 的成员证明，尚未定为 kernel bug |
| range / cart 字面枚举 | 短外延仍失败 | 补具体成员枚举/shape 证据；本次未宣称一般 cardinality 公式已解决 |

B12 一般 cart/符号区间基数没有在本轮重新证明，沿用历史未完成标记。
完整队列还有 44 个 gap，不等于 44 个独立 bug，也不是都需要改 Rust。

## 验收与证据

成功 release 的保留二进制 SHA-256：
`1b5c41a9d783edcb692f666bd8f5889bec8c9e7539325e85c5b9c313c0ae317f`。
在这个版本上，99 个正例文件（551 个独立用例）全部 strict 成功，284 个负例全部拒绝，
44 个残余 gap 均拒绝；B10 普通模式成功。81 个 persistent sketch 尝试均用独立 strict 文件重跑，
结果一致，包括错误结论、失败后继续和嵌套 index 控制。
数学负控不把 parser 拒绝当证明器的正确拒绝；原文/阶段分别记录。

第一次 current-source collector 构建在并发 `VerifyState` 编辑中失败，执行零个验收 fixture。
其诊断以及收尾构建检查都归档，不把保留二进制结果冒充后来源码的成功构建。
收尾构建再次 exit 101，仍是重复 VerifyState 定义和字段不匹配；没有当前源码正例验收。
9 个 runner 协议测试及 inventory audit 通过。本轮 diff 检查通过。
具体回执见 [acceptance](../../acceptance.md) 最新段落与 journal。

AST/fixture inventory 已通过。完整原文、Normal/Detailed 结果、修前源文件、promotion 映射、
本轮失败尝试、liveness 对照、全文件退出码与构建身份见
[proof journal](../../proof_journals/f_authoring_repairs_2026-10-03.json)。
历史审计和旧 journal 保留原始快照，退休 gap 的原文保存在新 journal 中。
