# 本轮排除的旧问题与已验解法 — 2026-10-04

最终复查release `cebcd18987723bca656be8143137ff690413f7d89735f3999e197838a0c46270`；本页是经验记录，不是活动问题列表。数学目标及原前提保留，没有添加证明trust或修改Rust。

当前99个Obj完整文件通过，309负例全部拒绝；完整作者路线和原短式分开记录。下列新增检查路径在持久session及干净strict文件均通过；其它现成路线的文件回执见本轮journal。

## OBJ12-checked-denominator

```litex
claim:
    ? forall a,b,c,d R:
        b!=0
        d!=0
        =>:
            a/b+c/d=(a*d+b*c)/(b*d)
    b*d!=0
    a/b+c/d=(a*d+b*c)/(b*d)
```

## OBJ13-checked-cancellation

```litex
have a R:
    a!=0
a*pi/a=pi
cos(a*pi/a+pi/2)=cos(pi+pi/2)=0
```

## OBJ14-checked-carrier-builder

```litex
let y=1
y $in R
let A={x R:x>y}
$is_set(A)
```

## OBJ14-checked-carrier-anonymous

```litex
let y=3
y $in R
fn(x R)R{x+y}(2)=2+y
```

## OBJ16-checked-powerset

```litex
{0} $in power_set(N)
have fn p(x power_set(N))power_set(N)={n N:(n+1) $in x}
p({0})={n N:(n+1) $in {0}}
```

## OBJ11-union-finiteness

```litex
# Node: atomic.ByBuiltinRule.LessEqual.FiniteSetSizeUnionLeSum
# Run: litex -f examples/proof_nodes/atomic/by_builtin_rule/less_equal_finite_set_size_union_le_sum.lit

$is_finite_set({1})
$is_finite_set({2})
$is_finite_set(union({1}, {2}))
finite_set_size(union({1}, {2})) <= finite_set_size({1}) + finite_set_size({2})
```

## LEG21-quotient-witness

```litex
claim:
    ? forall a Z,m N+:
        exist! q Z st {a=m*q+a%m}
    m!=0
    a=m*quot(a,m)+a%m
    witness exist! q Z st {a=m*q+a%m} from quot(a,m):
        claim:
            ? forall u,v Z:
                a=m*u+a%m
                a=m*v+a%m
                =>:
                    u=v
            m*u=a-a%m
            m*v=a-a%m
            u=(m*u)/m=(a-a%m)/m
            v=(m*v)/m=(a-a%m)/m
            u=v
```

## LEG24-constant-family-claims

```litex
claim:
    ? forall I,X set,S power_set(X):
        $is_nonempty_set(I)
        =>:
            index_union(I,X,fn(idx I)power_set(X){S})=S
    by extension:
        ? index_union(I,X,fn(idx I)power_set(X){S})=S
        claim:
            ? forall x index_union(I,X,fn(idx I)power_set(X){S}):
                x $in S
            obtain k from exist slot I st {x $in fn(idx I)power_set(X){S}(slot)}
            fn(idx I)power_set(X){S}(k)=S
            x $in S
        claim:
            ? forall x S:
                x $in index_union(I,X,fn(idx I)power_set(X){S})
            have k I
            fn(idx I)power_set(X){S}(k)=S
            x $in fn(idx I)power_set(X){S}(k)
            witness exist slot I st {x $in fn(idx I)power_set(X){S}(slot)} from k
            x $in index_union(I,X,fn(idx I)power_set(X){S})
```

## 其它已验完整路径

- finite_set_reduce、reduce_partition、finite_product_fresh_insertion、sum/product/有限聚合、fn_obj/tuple/序列载体、arctan/arccot/log、集合外延与互异：现存canonical作者文件通过。
- 原线代kernel目标、topology continuous_composition结尾、Newton返回R+的旧首败不重开；后续完整showcase失败另记在活动报告。
- callable模板别名、单字段旧例、dependent-signature正例与旧guard输入：按当前接口迁移通过；没有宣称旧unsupported拼写获得实现。
- strict冷/暖均拒绝含trust的0=1依赖；当前problem927释放函数定义后原跨文件目标通过。该修复/作者变更来自共享工作区，本任务不归因于自己。

[本轮活动报告](../../remaining_issues_current_2026-10-04.md) · [机器覆盖/原始证据](../../proof_journals/remaining_issues_current_2026-10-04.json)
