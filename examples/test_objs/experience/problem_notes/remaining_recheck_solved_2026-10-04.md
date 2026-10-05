# 剩余复核：已关闭项的解法与证据

任务来源：2026-10-04用户要求所有剩余问题重扫，汇报前确认已解决；解决后从活动纠错记录删除。当前102卡/69关闭/31开放/1暂缓/1持续开发的覆盖和固定身份见[机器记录](../../proof_journals/remaining_issues_recheck_2026-10-04.json)，旧具体活动记录全文及全部raw保留于[回执包](../../proof_journals/remaining_issues_recheck_2026-10-04_receipts.zip)。不据当前文件通过宣称全部数学/发布正确。

## 本轮关闭的原数学与作者问题

| 原卡 | 解法和验收 | 边界 |
| --- | --- | --- |
| LEG15/16/18/19/20/23/31/33 | 现有局部builtin分别处理rounding弱序、有界余数、阶乘整除、复数三角/反三角、LCM上界、cart重建、自然区间size。原式全部strict通过；10条附近错结论/缺前提及另1条字段arity控制保持拒绝。原式见下方。 | 数学缺口关闭；旧13规则目标的每族专用持久fixture和完整正负输出/replay验收仍待完成，不能因8式通过标目标完成。 |
| LEG34 | 在原a C非零、n N+域下显式消费幂非零、指数乘法与倒数定义的完整等式链通过。 | 原短式仍可搜索不到；已有同目标完整作者路线，所以不再报数学缺口。 |
| FN07 | field application builder及字段indexed-family发布已由源owner修复；三个原探针strict通过、最近错arity拒绝、真实新字段Rust gates通过。 | 已检原硬错误消失；输出来源缺项仍单列REL06。 |
| EX08/EX14 | 当前文件把原opaque积分关系/参数绑定改为已检声明和显式前提，两个完整strict文件通过、没有证明trust。 | 是原例子作者迁移；不是宣称任意积分值可以计算。 |
| SH06/SH07/SH11 | calculus、probability、numerical-analysis真实main.lit及配置-r完整通过。 | 原失败移出活动清单；不代替其它失败showcase。 |
| GEO03 | 源owner局部优先使用nonzero-real even-power证据，避免先完整寻找底数正性；新positive_real_power代码在本轮固定源码中；受影响完整Rust测试通过。 | 独立因果计时与反例见源owner验收，当前其它geometry门另列GEO01，不据此前缀计时宣称全部几何快/通过。 |
| M01–M04及M05原三卡点 | 8/9/10及citation/7完整已验；最新第6章23/23、第9章39/39配置复验通过。I07/I15原域/递推/结论；I16/C05遵循源owner记录的用户明确教学/域修订。 | I16原total算法不冒称与native零/负值域等价；canonical未动，R01/R02按用户要求暂缓。 |

源owner数学/模型边界：[字段与幂](../../../test_statements/experience/problem_notes/field-preimage-and-power-2026-10-04.md)、[Mechanics明确修订与验收](../../../../scripts/The-Mechanics-of-Litex-Proof/experience/problem_notes/2026-10-4-native-concepts-followup-acceptance.md)。

## 原通过输入

### LEG15

```litex
forall x,y R:
    x<=y
    =>:
        floor(x)<=floor(y)
        ceil(x)<=ceil(y)
```

当前strict成功；附近错结论/缺前提拒绝保留于final/extra-results.json。

### LEG16

```litex
forall a,q Z,m N+,r N:
    a=m*q+r
    r<m
    =>:
        a%m=r
```

当前strict成功；附近错结论/缺前提拒绝保留于final/extra-results.json。

### LEG18

```litex
forall m,n N:
    m<=n
    factorial(m) $in N+
    factorial(n) $in Z
    =>:
        factorial(n)%factorial(m)=0
```

当前strict成功；附近错结论/缺前提拒绝保留于final/extra-results.json。

### LEG19

```litex
forall z,w C:
    C_abs(z+w)<=C_abs(z)+C_abs(w)
```

当前strict成功；附近错结论/缺前提拒绝保留于final/extra-results.json。

### LEG20

```litex
forall z,w C:
    abs(C_abs(z)-C_abs(w))<=C_abs(z-w)
```

当前strict成功；附近错结论/缺前提拒绝保留于final/extra-results.json。

### LEG23

```litex
forall a,b Z*,m N+:
    m%abs(a)=0
    m%abs(b)=0
    =>:
        lcm(a,b)<=m
```

当前strict成功；附近错结论/缺前提拒绝保留于final/extra-results.json。

### LEG31

```litex
forall A,B,K set:
    $is_cart(K)
    cart_dim(K)=2
    proj(K,1)=A
    proj(K,2)=B
    =>:
        K=cart(A,B)
```

当前strict成功；附近错结论/缺前提拒绝保留于final/extra-results.json。

### LEG33

```litex
forall a,b N:
    a<=b
    =>:
        finite_set_size(range(a,b))=b-a
```

当前strict成功；附近错结论/缺前提拒绝保留于final/extra-results.json。

### LEG34原同域完整作者证明

```litex
claim:
    ? forall a C,n N+:
        a!=0
        =>:
            a^(-n)=1/(a^n)
    a^n!=0
    n*(-1)=-n
    (a^n)^(-1)=a^(n*(-1))
    (a^n)^(-1)=1/(a^n)
    a^(-n)=a^(n*(-1))=(a^n)^(-1)=1/(a^n)
```

原短搜索miss不再作为待修数学问题。源和persistent/clean回执均归档。

## 已存在的闭项本轮再次核验

Obj owning99/99、309负例、378 Stmt、175基础和规范226 fences符合预期。
非空fold/递归/有限性传递/分式/符号sum与product等已有完整路线保持；不把历史短式失败重新计问题。
跨模块原算术在同目标前加release obj def通过；完整numeric_power_rules和aggregate_identities重试通过。
原todo.md中22条direct gaps已经从manifest移除并有当前拥有者证明；旧todo全文保存在
record-before/examples/test_objs/todo.md，其原reproduction和当时诊断不再放活动列表。

## 输出源码消费者的局部拼写修正

两份本人既有constructor_order输出文件的形参language→lang，使固定match lang的源码检查通过。
前后文件字节及diff保存；当前source全部Rust846/847，唯一失败DEC04合同。重编译release与数学门
使用的099b9eff程序逐字节相同，没有更改AST、Runtime状态、搜索权限或验证语义。
