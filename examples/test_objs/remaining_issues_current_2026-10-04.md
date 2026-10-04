# 剩余问题现状复核 — 2026-10-04

本轮按总清单实际 **101张主题卡**（补入扫描期间新增的LEG33）逐项对照最新验收，再复测仍开放的原输入与既有解法。这里只列尚未收口的事项；已验证完整作者解法不作为问题。主题、失败次数、测试数均不等于独立kernel bug数。

最后冻结源码/测试manifest `f546d679b3dcf8b8983d8c81fd69ea7a8182ae0b04e33352412714d465664f05`，release `cebcd18987723bca656be8143137ff690413f7d89735f3999e197838a0c46270`。生产源码被并行更新时分四次冻结；最终重编译、复验结束的生产指纹与冻结指纹一致，各快照的结果不相加。

## 当前核验范围

| 集合 | 结果 |
| --- | --- |
| Obj owning文件 | 99/99，实际语句数不少于manifest正例数 |
| Obj负例 | 309/309正确拒绝 |
| Stmt | 50 leaves，378/378符合预期 |
| 基础合同 | 175/175 |
| 规范Markdown | 当前225/225；更新后的FAQ/Manual按其原普通模式123/123。另加strict对照116通过、7含trust按规定拒绝 |
| Rust最后完整固定门 | lib829/830，integration1/1；仅剩Point的phantom参数身份预期。exit101，完整门仍未通过 |
| 现有文件、旧输入与历史audit | 初轮1225输入含136个记录文件；47次65秒timeout只是覆盖/性能观察。最后1085个短式/作者路径/Obj/docs检查（含新增区间2式及更新文档123式）、10个完整失败showcase及模块对照，原始记录完整保存 |

原32项的活动详细记录现在只留下T05合同选择。其它数学目标已通过、作者例子已迁移或旧观察已撤回；旧证据留在archived_issues及zip，不把语法/modeling边界冒充内核修复。

完整生产collector/教材门尚未收口，所以上表不代表全库数学正确或完整发布通过。

## 执行、解析与输出

### FN07：字段函数原像命令仍会InternalBug

来源和函数签名先检查通过；以下原命令仍在构建字段application时发生硬错误。typed alias替代提取路线可用，但原字段命令的执行错误仍未修。

```litex
struct Ops:
    op fn(x R)R
    tag N
have fn shift(x R)R=x+1
have ops &Ops=(shift,0)
ops.op $in fn(x R)R
have by fn_preimage: a from ops.op(2) $in fn_range(ops.op)
```

实际：`internal_bug: ... cannot build application for ops.op`。owner是两个私有application builder的FieldAccess分支。字段indexed-family的两个短搜索miss已有完整alias路线，不另报告为数学问题；既有infer发布覆盖仍由该卡审计。

### LEG30：保留名被接受为binder，body却读取builtin

```litex
have fn picked(e R)R=e
picked(2)=e
```

当前接受，但body的e是EulerNumber，没有引用所声明的参数；`forall A,B,C set`里的C同样被解释成复数集合。不是“证明任意实数为正/任意集合非空”，是声明与引用身份不一致。parser入口仍未拒绝这些绑定。

### LEG27：模块限定struct类型仍解析失败

同一个二字段Pair定义已在已完成geo export内；根文件：

```litex
have item &geo::Pair=(1,2)
item.first=item.first
```

当前parse：`invalid parameter name ::`；完整小模块对照在receipt。此处没有拿缺Lib/config的孤立输入作证。

### REL05：algo已发布事实未进入Normal stores/infers

```litex
algo flag(x R)N by cases:
    case x=0: 0
    case x!=0: 1
flag $in fn(x R)N
flag(2)=1
```

数学与随后使用通过；algo定义项的Normal stores/infers仍空，cases Detailed也没有投影nested define_fn。原typed发布存在，这项是输出接线遗漏。

### REL06、LEG28：Detailed缺来源和真实失败payload

```litex
have f fn(x R)R
f(2) $in fn_range(f)
witness $is_nonempty_set(fn_range(f)) from f(2)
have y fn_range(f)
obtain a from exist x R st {y=f(x)}
```

成功obtain/preimage只输出stores，没有已检来源引用；arity失败以及finite enumeration/eval失败部分只输出success/kind。

```litex
witness exist x R st {x=0} from 0
obtain a,b from exist x R st {x=0}
```

```litex
by enumerate finite_set:
    ? forall k {1,2}:
        k=0
```

```litex
algo flag(x R)N by cases:
    case x=0: 0
    case x!=0: 1
let g=flag
eval g(2)
```

这些失败应保留拒绝；未解决的是把typed原因投影出来，不是要求错误枚举/错误arity成功。

## 原legacy数学目标尚无已验证完整路线

下面十三项原短式本轮仍拒绝；旧版本有实际通过证据，当前完整替代尚未验出。观察到search_proof/WD miss不等于已定位十三个规则bug；后续先定位原leaf与可检查作者证明。

### LEG12：有限乘积沿已证双射换指标

```litex
forall X,Y finite_set,g fn(y Y)X,f fn(x X)R:
    $bijective(Y,X,g)
    =>:
        finite_set_product(X,f)=finite_set_product(Y,fn(y Y)R {f(g(y))})
```

本次：拒绝；完整层级与WD/search在机器回执。没有确认共用根因。

### LEG13：已有运算律证书的无序 reduce 换指标

```litex
forall X,Y finite_set,g fn(y Y)X,f fn(x X)R,s R,op fn(a,b R)R:
    forall a,b,c R:
        op(op(a,b),c)=op(a,op(b,c))
    forall a,b R:
        op(a,b)=op(b,a)
    $bijective(Y,X,g)
    =>:
        finite_set_reduce(X,f,op,s)=finite_set_reduce(Y,fn(y Y)R {f(g(y))},op,s)
```

本次：拒绝；完整层级与WD/search在机器回执。没有确认共用根因。

### LEG14：有限和的不交并拆分，保留函数限制

```litex
forall A,B finite_set,f fn(x union(A,B))R:
    intersect(A,B)={}
    =>:
        finite_set_sum(union(A,B),f)=finite_set_sum(A,fn(x A)R {f(x)})+finite_set_sum(B,fn(x B)R {f(x)})
```

本次：拒绝；完整层级与WD/search在机器回执。没有确认共用根因。

### LEG15：BT：floor / ceil 保持弱序

```litex
forall x,y R:
    x<=y
    =>:
        floor(x)<=floor(y)
        ceil(x)<=ceil(y)
```

本次：拒绝；完整层级与WD/search在机器回执。没有确认共用根因。

### LEG16：BT：有界欧几里得余数唯一性

```litex
forall a,q Z,m N+,r N:
    a=m*q+r
    r<m
    =>:
        a%m=r
```

本次：拒绝；完整层级与WD/search在机器回执。没有确认共用根因。

### LEG18：BT / WD 消费：阶乘整除

```litex
forall m,n N:
    m<=n
    factorial(m) $in N+
    factorial(n) $in Z
    =>:
        factorial(n)%factorial(m)=0
```

本次：拒绝；完整层级与WD/search在机器回执。没有确认共用根因。

### LEG19：BT：复数模三角不等式

```litex
forall z,w C:
    C_abs(z+w)<=C_abs(z)+C_abs(w)
```

本次：拒绝；完整层级与WD/search在机器回执。没有确认共用根因。

### LEG20：BT：复数模反三角不等式

```litex
forall z,w C:
    abs(C_abs(z)-C_abs(w))<=C_abs(z-w)
```

本次：拒绝；完整层级与WD/search在机器回执。没有确认共用根因。

### LEG22：有限和的绝对值三角界

```litex
forall S finite_set,f fn(x S)R:
    abs(finite_set_sum(S,f))<=finite_set_sum(S,fn(x S)R {abs(f(x))})
```

本次：拒绝；完整层级与WD/search在机器回执。没有确认共用根因。

### LEG23：LCM 不超过正公共倍数

```litex
forall a,b Z*,m N+:
    m%abs(a)=0
    m%abs(b)=0
    =>:
        lcm(a,b)<=m
```

本次：拒绝；完整层级与WD/search在机器回执。没有确认共用根因。

### LEG31：已知维数及逐因子投影的Cartesian equality重建

```litex
forall A,B,K set:
    $is_cart(K)
    cart_dim(K)=2
    proj(K,1)=A
    proj(K,2)=B
    =>:
        K=cart(A,B)
```

本次：拒绝；完整层级与WD/search在机器回执。没有确认共用根因。

### LEG32：有限索引与逐项有限到索引并集有限

```litex
forall I nonempty_set,X set,A fn(idx I)power_set(X):
    $is_finite_set(I)
    forall k I:
        $is_finite_set(A(k))
    =>:
        $is_finite_set(index_union(I,X,A))
```

本次：拒绝；完整层级与WD/search在机器回执。没有确认共用根因。

### LEG33：符号自然数端点的区间基数

以下两个原目标在 `a,b N`、`a<=b` 条件下仍在search_proof拒绝；完整作者替代尚未验出。字面端点计数通过不能代替泛化目标。

```litex
forall a,b N:
    a<=b
    =>:
        finite_set_size(range(a,b))=b-a
```

```litex
forall a,b N:
    a<=b
    =>:
        finite_set_size(closed_range(a,b))=b-a+1
```

## 例子与数学主体尚未完成

这些是保留原目标的作者迁移/证明债，不能直接当作内核缺规则。原已解决步骤不会在此重报。

| 卡 | 当前仍开放的具体输入/位置 | 状态 |
| --- | --- | --- |
| EX07 | dihedral草稿的`trust forall m Z:`带缩进body | parse要求trust:；其数学背景也未无trust完成 |
| EX08 | `trust have probe_integral fn(f fn(x R)R)R`及原线性性质背景 | 当前减法目标作者链通过；三处opaque背景trust仍在 |
| EX13 | `tuple_dim(symbolic_tuple)=m`和`tuple_dim(tuple_from_member)=m` | 固定n=3部分已通过；两个符号维数构造的旧声明仍注释，symbolic_tuple未定义，作者迁移未完 |
| EX14 | `trust $alpha_assumption(fn(k R)R{k})` | 四个trust seed尚未迁为显式输入条件 |

以下十个主体文件用最终binary重新跑，均有实际失败结果；第1章65秒timeout另属性能/未验收，不当作已证数学错误。

### 13_numerical_analysis_in_nutshell-main

源文件：[showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell/main.lit](../../showcases/math_concepts_in_litex/13_numerical_analysis_in_nutshell/main.lit)。本次exit `1`、Run.success=false。以下为完整上下文中的首败片段，不是独立可运行代码。

```litex
f0::sqrt_two_newton_gap(n) ^ 2 / 4 $in R
```

### 8_probability_and_statistics_in_nutshell-main

源文件：[showcases/math_concepts_in_litex/8_probability_and_statistics_in_nutshell/main.lit](../../showcases/math_concepts_in_litex/8_probability_and_statistics_in_nutshell/main.lit)。本次exit `1`、Run.success=false。以下为完整上下文中的首败片段，不是独立可运行代码。

```litex
(values(1) - f0::expectation2(values, probs)) ^ 2 * probs(1) + (values(2) - f0::expectation2(values, probs)) ^ 2 * probs(2) $in R
```

前序定义失败后又出现未定义名字；这是连锁结果，不另计根因。完整错误保留在receipt。

### 7_calculus-main

源文件：[showcases/math_concepts_in_litex/7_calculus/main.lit](../../showcases/math_concepts_in_litex/7_calculus/main.lit)。本次exit `1`、Run.success=false。以下为完整上下文中的首败片段，不是独立可运行代码。

```litex
(f(x) - f(x0)) / (x - x0) - L $in R
```

### 9_topology-main

源文件：[showcases/math_concepts_in_litex/9_topology/main.lit](../../showcases/math_concepts_in_litex/9_topology/main.lit)。本次exit `1`、Run.success=false。以下为完整上下文中的首败片段，不是独立可运行代码。

```litex
fn (x K) Y{f(x)}(point) = f(point)
```

### 11_multivariable_calculus_in_nutshell-main

源文件：[showcases/math_concepts_in_litex/11_multivariable_calculus_in_nutshell/main.lit](../../showcases/math_concepts_in_litex/11_multivariable_calculus_in_nutshell/main.lit)。本次exit `1`、Run.success=false。以下为完整上下文中的首败片段，不是独立可运行代码。

```litex
f0::quadratic_surface((x, p[2])) = x ^ 2 + p[2] ^ 2
```

### 12_ordinary_differential_equations_in_nutshell-main

源文件：[showcases/math_concepts_in_litex/12_ordinary_differential_equations_in_nutshell/main.lit](../../showcases/math_concepts_in_litex/12_ordinary_differential_equations_in_nutshell/main.lit)。本次exit `1`、Run.success=false。以下为完整上下文中的首败片段，不是独立可运行代码。

```litex
(f(x) - f(x0)) / (x - x0) - slope $in R
```

前序定义失败后又出现未定义名字；这是连锁结果，不另计根因。完整错误保留在receipt。

### 4_discrete_mathematics_in_nutshell-main

源文件：[showcases/math_concepts_in_litex/4_discrete_mathematics_in_nutshell/main.lit](../../showcases/math_concepts_in_litex/4_discrete_mathematics_in_nutshell/main.lit)。本次exit `1`、Run.success=false。以下为完整上下文中的首败片段，不是独立可运行代码。

```litex
strategy predecessor_sum_bounds:
    ? forall a, b Z:
        a > 0
        b >= 0
        =>:
            a - 1 + b >= 0
            b + (a - 1) >= 0
    a - 1 >= 0
```

随后Pascal递归还在调用guard `a-1>=0` 的WD检查失败；前序定义失败后的pascal_entry未定义不另算独立问题。

### 6_abstract_algebra-main

源文件：[showcases/math_concepts_in_litex/6_abstract_algebra/main.lit](../../showcases/math_concepts_in_litex/6_abstract_algebra/main.lit)。本次exit `1`、Run.success=false。以下为完整上下文中的首败片段，不是独立可运行代码。

```litex
add_B(zero_B, zero_B) = zero_B
```

原homomorphism输入未提供所需的环运算律；先补齐数学模型的前提，不能由此断定内核缺规则。

### 14_tarski_geometry_from_axioms-main

源文件：[showcases/math_concepts_in_litex/14_tarski_geometry_from_axioms/main.lit](../../showcases/math_concepts_in_litex/14_tarski_geometry_from_axioms/main.lit)。本次exit `1`、Run.success=false。以下为完整上下文中的首败片段，不是独立可运行代码。

```litex
(a, b, b) $in Bet
```

### 2_euclidean_geometry-main

源文件：[showcases/math_concepts_in_litex/2_euclidean_geometry/main.lit](../../showcases/math_concepts_in_litex/2_euclidean_geometry/main.lit)。本次exit `1`、Run.success=false。以下为完整上下文中的首败片段，不是独立可运行代码。

```litex
f0::vec(a, b)[1] * f0::vec(a, b)[1] + f0::vec(a, b)[2] * f0::vec(a, b)[2] = (b[1] - a[1]) ^ 2 + (b[2] - a[2]) ^ 2
```

### SH01：第1章variance3返回载体仍失败，整章尚未验收

```litex
have fn mean3(a, b, c R) R = (a + b + c) / 3
have fn variance3(a, b, c R) R = ((a - mean3(a, b, c))^2 + (b - mean3(a, b, c))^2 + (c - mean3(a, b, c))^2) / 3
```

当前mean3定义通过；variance3的函数体WD通过，但函数体属于R的检查在search_proof失败。完整第1章原上下文65秒未返回完成结果，记为未验收/性能观察。不能据独立片段否定整章数学，也不能用179条已通过前缀代替整章。

## 教材的剩余原数学及推广

### M01–M05：Mechanics草稿与canonical不同

当前复制草稿第0/1/3/5/9/10章strict完整通过；2/4章仍各一trust，6/7/8有真实后续失败，实际整书ordinary入口FailToImport。原canonical42处trust及推广未完成不等于42个kernel bug。

尚未恢复/关闭的具体目标：

```litex
# T05：n Z，原整数平方不等于2
forall n Z:
    n^2!=2
# T40：a Z, m N+, k N, k<m，给定商余分解
forall a Z,m N+,k N:
    k<m
    exist r Z st {a=m*r+k}
    =>:
        a%m=k
```

```litex
# D03已有 c N、c!=0 证据，当前辅助链还卡在
c $in N+
# D13两方向分别可证；原合并forall-iff包装仍失败
forall a Q:
    =>:
        a<=2
    <=>:
        3*a+1<=7
```

```litex
# 第6章保留a=0等合法情况时，幂/congruence的WD和代数链未完成
$mod_eq(a^n,b^n,d)
# 第7章仍引用未导出的非primitive接口
release thm citation::bezout_identity(a,d)
# 第8章Cantor pairing仍有原后续步骤未通过
0*((n+1)%2)%2=0%2
```

上面省略的原前提与完整保留证明在Mechanics source-owned todo/journal。本轮也重新跑了T05/T40/D03/D13原完整独立输入；仍拒绝，不凭其一个辅助step宣布缺某个builtin。

## 合同边界、性能与验收

### DEC01：by contra的量词嵌套反假设仍不支持

```litex
by contra:
    ? forall x {0}:
        exist y {0} st {y=x}
    impossible 0=0
```

当前reverse assumption阶段`negation_unsupported`。现有QF-only载荷无法保存∃x∀y，数学目标可以用别的普通证明表达；这里尚未完成的是承诺的该by-contra输入覆盖，不能叫简单数值计算bug。

### DEC02：trust body的WD顺序合同

```litex
trust have x R:
    x!=0
    1/x=1/x
```

non-strict当前整体预WD拒绝；按源序分条trust有已验路线。该块语义待维护者选择，不列为数学目标不能证明。strict拒绝trust是规定边界。

### DEC03、EX09：旧公开表面是否恢复

```litex
example:
    ? 0=0
+ = +
```

旧ExampleStmt、有限集合induc表面、have-algo-for、DefSetting/旧method等去留仍是兼容性决定。普通目标/集合归纳/算法已有checked迁移路线；这里只记录旧接口合同，非重新报告这些数学目标失败。

### DEC04／原T05：phantom参数身份

```litex
struct Point<K nonempty_set,S nonempty_set>:
    value S
    tag N
forall t &Point<N,R>:
    t $in &Point<Z,R>
```

当前接受；K不参与字段，两个实例可能表示同一字段集合。需要选择字段集合语义或所有参数的名义身份。没有证出错误数值等式；实际不符合字段类型与wrong value控制仍拒绝。

### DEC05：实指数/依赖表面的域合同

```litex
forall x R+:
    x^(1/3)=x^(1/3)
```

当前仍拒绝，必须核对当前支持指数域与数学合同，不能仅为自反式放宽WD。合法固定codomain族已可用，旧dependent-return拼写的合同尚未恢复。

### GEO01/GEO03/SH13：真实消费者、性能、原axiom债

```litex
# 示意旧profile涉及的表达式，不是本轮新复现；原AAS上下文只知det非零
have H R=det(u,v)^2
# 多次平方入库附加正性推理的长搜索仍需原消费者验收。
# problem207保留原axiomatic target declarations；不是无axiom证明。
```

完整geo生产者/所有消费者、三处原axiom债及等价/引用活性没有用少数green替代。47次65秒timeout保留为未完成/性能证据，不宣称47个bug。旧profile的86/120秒来源尚未在最终版本做插桩，因此不把嫌疑owner写成已确认因果。

### REL02/REL04/LEG29：完整库存和replay验收仍开放

```sh
cargo test --release --offline --all-targets --no-fail-fast
cargo test --release run_examples_only
cargo test --release run_showcases
```

零选择已经会判失败，但生产完整collectors仍未恢复/完整执行；historical audit fences混有故意负例、缺上下文与旧短式，不能统一expect=false或批量skip。动态owner/独立证据replay尚未形成完整覆盖证明。这是验收缺口，当前strict-cache0=1和problem927已关闭。

## 覆盖与证据

实际101卡：开放51、已关闭或已有完整解法49、用户持续开发但不列bug1。open含合同、证明债、覆盖和性能，不能当成独立bug数。所有原32项逐条处置，具体活跃T05留在旧活动纠错记录。

[已排除解法与闭环](experience/problem_notes/remaining_scan_solved_2026-10-04.md) · [101卡机器矩阵](proof_journals/remaining_issues_current_2026-10-04.json) · [所有输入、source、binary与原输出](proof_journals/remaining_issues_current_2026-10-04_receipts.zip)
