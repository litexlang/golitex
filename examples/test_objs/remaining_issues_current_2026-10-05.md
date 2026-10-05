# 剩余问题现状复核 — 2026-10-05

> 迁移审计补证（同一84d13156）：五项原短例与近邻错误输入再次符合预期；另记录abs双侧界作者桥、FnRange小工具及多签名WD排除。见[专项原例与raw](../../plan/迁移的plan/legacy-finite-sum-index-union-audit-2026-10-05.md)。本补证未实施共享规则，不代替下方实施/完整门回执。

任务来源：用户要求剩下的所有问题全部重扫，汇报前确认是否已经解决；已解决的具体纠错记录移出活动列表。本文只列仍未完成的事项，原编号不重排。

总清单102张主题卡：75张已验证关闭或有同目标完整作者路线，**25张仍开放**，1张教材集成/推广按来源记录由用户暂缓，1张持续开发排除。这些是维护主题，不是25个独立内核bug。已通过的原目标从具体纠错清单删除，解法与前后证据保存到source-owned经验/journal。

最终标准release SHA256 `84d13156c18623fafcf14c646a27fe8efe0b625f0b2d682cdd2cf562604c8fe9`，与隔离Cargo缓存构建逐字节相同。生产src/Cargo manifest摘要 `2b133ef3908ae412b698eae7ec2243a77439ea92efb8c462faf0613b20438623`（SHA256 of sorted JSON manifest）。本次重新构建后针对剩余25张卡执行92条逻辑输入、89次实际进程，检查全部49个几何consumer、实际showcase与真实模块配置；源码和二进制期间稳定。

| 最新真实检查 | 结果和边界 |
| --- | --- |
| 剩余卡逐项复验 | 88次去重进程，另1次共享更新后的整文件复验，以及实际Normal/Detailed投影、source/collector覆盖检查。仅保留未完成事项。 |
| Obj拥有者 | 当前release99/99完整文件通过，登记666正例；309/309负例正确拒绝；manifest gap为0。 |
| 完整数学入口 | 下列六个showcase仍实际拒绝；中学数学整文件120秒超时。 |
| 几何完整consumer | 49个：1通过、4明确拒绝、44个60秒超时；完整共享producer亦60秒超时。超时表示预算内未完成，不能算数学bug。 |
| 局部规则验收 | 54项非零选择的针对性Rust测试通过；当前已完成目标均不再列为问题。 |
| Rust完整门 | 最新lib862/863、integration1/1；唯一红断言DEC04仍失败，命令exit101，不能宣称全绿。 |
| 文档/覆盖 | REL04当前collector仍选中历史audit的`1 = 2`为正例；REL02两旧filter仍各选0测试；LEG29原独立method/replay全覆盖仍未验。规范文档226/226是修复前完整审计，未冒充本次重新跑全量docs。 |

ODE源文件在扫描期间由共享工作更新，旧失败已被新完整文件strict成功回执替代并移出列表；新输入前后hash稳定。当前代码与失败位置只按最后复验记录。

此前同日975次去重进程覆盖102卡的完整扫描与846/847 Rust旧截面保留为[历史完整机器记录](proof_journals/remaining_issues_recheck_2026-10-05.json)和[原回执包](proof_journals/remaining_issues_recheck_2026-10-05_receipts.zip)。它们属于修复前固定source/binary；不改写其中的31卡观察。本次增量复验及最终源码/回执见[新完成journal](proof_journals/thirteen_builtin_rules_2026-10-05.json)及配套zip。

解析/合同小例为完整探针；showcase和几何的代码为实际完整文件的失败片段，须保留原声明与前提。历史无上下文片段没有用于判断当前数学问题。用户暂缓的整书项目没有重开。

## 解析和输出的五张卡

### LEG30：保留名接受为参数，引用却读取builtin

```litex
have fn picked(e R)R=e
picked(2)=e
```

当前接受，但函数body读取Euler常数，而非声明的参数e。同输入改结论为`picked(2)=2`拒绝；参数改名t后同一identity目标通过。`C`也有同类声明/引用冲突。已检控制排除了“任意数为正/任意集合非空”的旧夸大说法。归属：局部parser validation候选；下一步统一保留名声明与引用合同。验收要覆盖函数、量词与实际绑定身份，不能只修打印名称。

### LEG27：模块限定struct类型解析失败

真实配置先export二字段`geo::Pair`，主文件：

```litex
have item &geo::Pair=(1,2)
item.first=item.first
```

parse返回`invalid parameter name ::`。回执保留geo.lit和litex.config，未用缺模块定义的孤立输入。归属：限定struct parser入口；下一步沿已导出的名字解析类型。验收为同配置strict成功，未导出的名字和错误字段仍拒绝。

### REL05：algo发布事实没有投影到输出

```litex
algo flag(x R)N by cases:
    case x=0: 0
    case x!=0: 1
flag $in fn(x R)N
flag(2)=1
```

计算、事实存储和后续使用通过；定义项Normal的stores/infers为空，Detailed未展示nested define_fn。是JSON接线遗漏。下一步按实际typed发布结果投影，而非补虚构事实；验收检查定义项自身、后续FactId消费与失败不发布。

### REL06：obtain/preimage来源与失败payload没有投影

```litex
have f fn(x R)R
f(2) $in fn_range(f)
witness $is_nonempty_set(fn_range(f)) from f(2)
have y fn_range(f)
have by fn_preimage: a from y $in fn_range(f)
```

完整前提下命令成功；Detailed只有stores，没有已检source membership及来源证明。相同前缀改用`obtain a from exist x R st {y=f(x)}`也缺来源投影。错误arity例子：

```litex
witness exist x R st {x=0} from 0
obtain a,b from exist x R st {x=0}
```

正确拒绝；Detailed失败项仅`success:false,kind:obtain_obj_from_exist_fact`，丢了原因。归属：局部JSON投影；下一步保留typed子结果与引用，验收成功来源和失败原因两条路径。

### LEG28：eval和有限枚举的Detailed失败原因丢失

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

两条当前均拒绝；Detailed只给失败kind，缺真实typed原因。这里要求补诊断，不要求错误枚举通过，也不把已完成的eval结果等式存储问题重开。归属：JSON投影；验收保持拒绝，输出具体失败阶段/子结果。

## 仍失败的完整数学例子

下面六个main.lit均在当前release真实退出1/root false。按实际首败列出，后续undefined-name或FailToImport只作为连锁，不能另计根因。归属暂为作者证明/定义；先做可检查步骤，定位局部内核根因后再提出修复。验收是原完整文件及实际模块入口strict通过，保留原域、前提、结论。

| 卡 | 完整来源 | 当前失败表达式/阶段 | 下一步 |
| --- | --- | --- | --- |
| SH02 | [欧氏几何](../../showcases/math_concepts_in_litex/2_euclidean_geometry/main.lit) | `vec(a,b)[1]*vec(a,b)[1]+vec(a,b)[2]*vec(a,b)[2]=(b[1]-a[1])^2+(b[2]-a[2])^2`；等式链第二相邻项search失败 | dot展开已过；补坐标展开与代入的检查链。 |
| SH03 | [离散数学](../../showcases/math_concepts_in_litex/4_discrete_mathematics_in_nutshell/main.lit) | `strategy predecessor_sum_bounds`拒绝；其body为`a-1>=0`，前提`a,b Z,a>0,b>=0` | 检查整数前驱界并完成原Pascal定义及后段；不能把下游pascal_entry未定义当新bug。 |
| SH05 | [抽象代数](../../showcases/math_concepts_in_litex/6_abstract_algebra/main.lit) | `add_B(zero_B,zero_B)=zero_B`，chain第三相邻项search失败 | 源定义缺相应环/加法单位元律，先完善数学前提及其归属；当前不能由任意函数推出该式。 |
| SH08 | [拓扑](../../showcases/math_concepts_in_litex/9_topology/main.lit) | `fn(x K)Y {f(x)}(point)=f(point)`；WD已过、search失败 | 完成连续复合证明中的restriction/beta步骤。 |
| SH09 | [多元微积分](../../showcases/math_concepts_in_litex/11_multivariable_calculus_in_nutshell/main.lit) | `quadratic_surface((x,p[2]))=x^2+p[2]^2`；WD已过、search失败 | 检查函数体展开与tuple投影的代入。 |
| SH12 | [Tarski几何](../../showcases/math_concepts_in_litex/14_tarski_geometry_from_axioms/main.lit) | `(a,b,b) $in Bet`；search失败 | 明确消费实际betweenness公理/已证引理。 |

### GEO01：几何下游还有实际失败与未完成验收

49份solution.lit均保留真实config/import上下文。problem_13的当前首败是用户函数体的复合代入：

```litex
((1-u)-v)*dist_A(a,c,s,u,v)+u*dist_B(a,c,s,u,v)+v*dist_D(a,c,s,u,v)
    =((1-u)-v)*((u*a+v*c)^2+(v*s)^2)
        +u*(((u-1)*a+v*c)^2+(v*s)^2)
        +v*((u*a+(v-1)*c)^2+((v-1)*s)^2)
```

完整file的WD通过，该等式search失败。problem_870、928、934的solution在import处拒绝；追到各自translation.lit后，首败与SH02同形，是vec坐标平方代入。只确认相同失败步骤，未确认一个Rust共用根因。

最新release复验49个consumer：1通过、4实际拒绝、44个60秒超时；共享geo生产者完整入口本次亦60秒超时。超时编号与raw逐一保存，没有把它们计成同数量的数学bug。

归属：作者展开/模块集成及性能验收。下一步分别关闭上述实际数学步骤和真实完整producer→consumer门；超时仅表示本次预算未完成，不表示定理错误。历史scripts/geo.lit的227/227长门不冒充当前全模块复验。原源码、每个问题编号与命令都在journal。

### EX13：两处符号维数tuple构造仍缺代码

[实际文件](../_internal/regression/generic_cart_member_coordinates.lit)第103行：

```litex
# TODO: removed have-indexed stmt; use have fn
# have tuple symbolic_tuple for i1 <= m, symbolic_tuple[i1] = 0
tuple_dim(symbolic_tuple)=m
```

parse为`undefined name symbolic_tuple`；后段tuple_from_member同样只留下被注释的旧构造。旧c未定义的片段已失效，不再报告。归属：作者接口迁移；需实现同一符号m的构造并验完整后段，固定n=3不能关闭这项。

### EX07：dihedral草稿仍有8处trust

[当前草稿](../_internal/drafts/dihedral_group_isomorphism_draft.lit)普通模式完整65项通过，旧inline-trust缩进语法已经迁移。仍有1处单语句trust及7处trust块，包括：

```litex
trust:
    forall G set,r,f G:
        $presentation_r8_f2_rfrf(G,r,f)
        =>:
            $presentation_reflection_swap_rule(G,r,f)
```

剩余是背景presentation universal property、word reduction、cardinality、surjection等证明债；strict按规定拒绝trust。归属：数学模型/作者证明，不能为过门禁新添trust。验收是原数学接口的完整无trust证明及strict file gate。

### SH13：showcase内容一致性和problem207尚未完整收口

problem207目前**没有原先三条axiom声明**，旧记录已失效；[当前source](../../showcases/math_concepts_in_litex/15_coordinate_geometry_case_study/problem_207/solution.lit)明确只形式化第(2)问。第(1)、(3)问原文保留，但不是主定理的结论：

```text
(1) F为CD中点时，证明AE=BE+2CE。
(3) 若CG=DF，证明HG垂直AG。
```

这两问仍无已验完整证明；第(2)问完整consumer本轮60秒仍超时。除此之外，原showcase的全部数学合同、引用活性/删除反事实、完整公开入口的覆盖尚未全部验收。归属：内容/证明/验收；下一步对照原问题逐项检查，不从名字齐全或零trust推断数学等价。

## 五项合同以及旧接口迁移

这些不是已经定责的健全性bug。本轮只确认行为，不擅自改AST、struct身份、trust或幂的数学域。

### DEC01：反证的嵌套量词表示

```litex
by contra:
    ? forall x {0}:
        exist y {0} st {y=x}
    impossible 0=0
```

reverse-assumption阶段`negation_unsupported`：existing NotForall cannot represent an existential conclusion。普通forall-exist可通过，不等于此反证表示已支持。归属：量词否定表示合同；下一步决定可表示的嵌套范围/复杂度后给具体实现，不能凭这个例子自行改Fact AST。

### DEC02：trust-have body的WD顺序

普通模式输入：

```litex
trust have x R:
    x!=0
    1/x=1/x
```

整体预WD先拒绝第二句，未消费第一句的非零证据；按源序分开的当前写法可用。待定的是命令先整体预检还是逐句WD→trust。strict拒绝任何trust是既定边界。归属：执行顺序合同；验收需合法依赖、错误WD、失败回滚与strict控制。

### DEC03、EX09：移除的公开接口没有逐项兼容/替代收口

```litex
example:
    ? 0=0
```

```litex
+ = +
```

分别parse为`undefined name example`和`expected object, got +`。第一条的数学`0=0`本身通过；第二条是旧operator-object自反表面，不是数字加法失败。ExampleStmt、setting/forall[Setting]、旧try、finite-set induction、replacement分别仍需核对删除决定及同意图完整替代。归属：兼容/作者迁移合同；原输入保留，不能改成新语法后说旧接口已恢复。

### DEC04：Point未使用参数的身份

```litex
struct Point<K nonempty_set,S nonempty_set>:
    value S
    tag N
forall t &Point<N,R>:
    t $in &Point<Z,R>
```

当前接受。K没有用于字段，两实例都描述R×N的tuple；因此这个接受不能直接认定不健全。完整Rust门唯一失败也要求此类输入拒绝。待定是原例应该写tag K，还是未使用K仍必须区分身份。归属：模型/测试或一致struct表示合同；不只挡membership而保留相同外延定义。

### DEC05：一般正实底数的有理/实指数域

```litex
have x R+
x^(1/3)=x^(1/3)
```

Pow WD拒绝，当前路径要求`1/3 $in Z`。原forall版本也拒绝；部分闭数字幂通过不能替代一般正实底数合同。归属：数学域/接口决定；下一步明确支持的指数域与零/负底数边界，再实现和验收。已有0^0和零负指数拒绝保持。

## 超时和验收覆盖

### SH01：中学数学整文件仍未完成门禁

最新[main.lit](../../showcases/math_concepts_in_litex/1_middle_school_math_in_nutshell/main.lit)已包含更新的算术数列显式展开；安静重试120秒仍超时，没有完成JSON回执。原variance3返回载体失败已解决，不再报告。当前只报完整文件/模块性能验收未完成；下一步定位耗时段，再验真实全文件。

### REL02：完整发布验收没有全绿

```sh
cargo test --release --offline --all-targets --no-fail-fast
cargo test --release --offline run_examples_only
cargo test --release --offline run_showcases
```

第一条最新lib862通过、1失败（DEC04），integration1通过，exit101；后两条仍各选择0个测试。零测试假绿的判定已修，本项剩的是恢复真实collector/库存以及完整发布验收；不能用过滤器exit0或scoped数学通过代替。下一步在收尾后的固定source/binary运行Rust、真实examples/showcase/docs/教材及owner门，并记录非零选择和JSON/exit。

### REL04：历史audit失败代码还被当正例收集

实际collector还会独立执行[旧audit](../../docs/audits/examples-migration-rescan-2026-10-02.md)第2088行：

```litex
1=2
```

正确拒绝，但collector对所有未skip fences要求成功。规范文档226/226通过不解决历史audit的期望分类。归属：文档测试collector；下一步明确负例/片段的预期及上下文，保留错误算式拒绝。

### LEG29：完整动态分支和独立evidence replay覆盖未完成

具体既有表：[legacy动态覆盖](../../plan/迁移的plan/proof_journals/legacy-dynamic-coverage-2026-10-04.json)。最新selected module/replay审计实际只有65/460个精确method token命中；例如已有`fn_set_member`模块模板consumer通过，不证明其余owner/分支已经运行：

```litex
have fn picked(x R)R=x
picked $in fn(x R)R
```

此处是验收工作边界，不是该identity例子失败。parser→WD→store→use→Normal/Detailed→独立replay、模块/cache/rollback各分支尚需真实配对证据。下一步按owner映射补缺项，不能把静态方法数、通用equality token或JSON解析计成独立proof replay成功。

### M05：教材整书集成与canonical推广由用户暂缓

第6章新完整配置23/23、第9章39/39、citation/第7章已验；旧I07/I15以及按用户最新教学决定修订的I16/C05都已移出失败列表。这里仅保留R01真实整书集成、R02canonical推广/公开同步，依来源专项记录由用户暂缓。本轮没有重开这两项工作，也不把先前FailToImport当新稿仍失败的证据：

```sh
litex -strict -r scripts/The-Mechanics-of-Litex-Proof/.draft/2026-10-2-stmt-body-continuation/textbook
```

这是真实后续验收入口，**本轮最新稿未执行**。canonical17文件仍42trust；局部草稿通过不表示已推广。恢复范围后再验原整书与发布同步。

## 记录维护和复现

活动入口为[总计划](../../plan/src收尾总清单.md)和[Obj todo](todo.md)。本次已解原目标移出活动纠错记录；当前25张开放卡均有新版输入/文件或输出/源码覆盖证据。过去的失败报告、解法和固定回执保持历史身份，不能拿它们推断当前失败。

回执包保存本轮literal输入、完整输出、扫描脚本、新编译release和Detailed helper，以及当前源码和实际配置/fixture快照。`archive-index.json`将路径和权限映射到内容寻址blob；按索引恢复后将回执中的绝对路径映射到恢复目录。Rust测试需在恢复根重新编译，以免沿用编译时的原始`CARGO_MANIFEST_DIR`。

本次在原授权内完成13类局部builtin目标和持久回归/typed/输出验收；具体解法及限制在source-owned经验。没有AST/Env/Runtime状态改型、扩大全局搜索权限、新trust、commit或发布。完整发布、教材推广及全460种独立replay仍按下面开放卡/暂缓项记录，不能由局部验收代领。
