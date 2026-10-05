# 十三类局部数学规则的完成验收 — 2026-10-05

Task context：用户 `/goal` 授权将 LEG12–16、18–20、22–23、31–33 的13类原数学目标补为局部 builtin rules；随后要求重扫剩余问题，汇报前确认是否已解决，关闭项从具体纠错记录删除。

最终源码编译的标准 `target/release/litex` 与隔离缓存构建逐字节一致，SHA256 `84d13156c18623fafcf14c646a27fe8efe0b625f0b2d682cdd2cf562604c8fe9`。14份原输入（区间两种）全部 strict exit0 / root success true；15份独立持久 tracer 全部通过。验收字段来自真实执行；不以输出文本或零测试过滤器代替。

54项非零选择的针对性 Rust 测试通过：新增规则总验收8、有限换指标8、已有局部能力13+7+7、聚合6、单元素有限reduce1、语言源码合同3、实际枚举语言consumer1。原式、所选反向/alpha与一般fold载体、缺前提、错误函数/域/binder、错误运算/seed和缺AC均有执行控制。十语言Normal/Detailed producer和真实胜出leaf解释均消费同一typed证据。未声称完整发布门、460种legacy独立replay或Lean证书导出已经完成。

## 原输入与持久验收

原代码没有改前提或结论，历史 proof_search 拒绝与现在成功对应同一输入。每个持久文件保留注释的旧代码、活跃的当前代码和CLI命令；可执行负例在测试中。

### LEG12

```litex
forall X,Y finite_set,g fn(y Y)X,f fn(x X)R:
    $bijective(Y,X,g)
    =>:
        finite_set_product(X,f)=finite_set_product(Y,fn(y Y)R {f(g(y))})
```

- `FiniteSetProductReindex`：[独立tracer](../../../proof_nodes/equal/by_builtin_rule/finite_set_product_reindex.lit)。
### LEG13

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

- `FiniteSetReduceReindex`：[独立tracer](../../../proof_nodes/equal/by_builtin_rule/finite_set_reduce_reindex.lit)。
### LEG14

```litex
forall A,B finite_set,f fn(x union(A,B))R:
    intersect(A,B)={}
    =>:
        finite_set_sum(union(A,B),f)=finite_set_sum(A,fn(x A)R {f(x)})+finite_set_sum(B,fn(x B)R {f(x)})
```

- `FiniteSetSumDisjointUnion`：[独立tracer](../../../proof_nodes/equal/by_builtin_rule/finite_set_sum_disjoint_union.lit)。
### LEG22

```litex
forall S finite_set,f fn(x S)R:
    abs(finite_set_sum(S,f))<=finite_set_sum(S,fn(x S)R {abs(f(x))})
```

- `FiniteSetSumTriangle`：[独立tracer](../../../proof_nodes/atomic/by_builtin_rule/finite_set_sum_triangle.lit)。
### LEG32

```litex
forall I nonempty_set,X set,A fn(idx I)power_set(X):
    $is_finite_set(I)
    forall k I:
        $is_finite_set(A(k))
    =>:
        $is_finite_set(index_union(I,X,A))
```

- `FiniteIndexUnion`：[独立tracer](../../../proof_nodes/atomic/by_builtin_rule/finite_index_union.lit)。
### LEG15

```litex
forall x,y R:
    x<=y
    =>:
        floor(x)<=floor(y)
        ceil(x)<=ceil(y)
```

- `FloorMonotone`：[独立tracer](../../../proof_nodes/atomic/by_builtin_rule/floor_monotone.lit)。
- `CeilMonotone`：[独立tracer](../../../proof_nodes/atomic/by_builtin_rule/ceil_monotone.lit)。
### LEG16

```litex
forall a,q Z,m N+,r N:
    a=m*q+r
    r<m
    =>:
        a%m=r
```

- `EuclideanRemainder`：[独立tracer](../../../proof_nodes/equal/by_builtin_rule/euclidean_remainder.lit)。
### LEG18

```litex
forall m,n N:
    m<=n
    factorial(m) $in N+
    factorial(n) $in Z
    =>:
        factorial(n)%factorial(m)=0
```

- `FactorialDivisibility`：[独立tracer](../../../proof_nodes/equal/by_builtin_rule/factorial_divisibility.lit)。
### LEG19

```litex
forall z,w C:
    C_abs(z+w)<=C_abs(z)+C_abs(w)
```

- `ComplexTriangle`：[独立tracer](../../../proof_nodes/atomic/by_builtin_rule/complex_triangle.lit)。
### LEG20

```litex
forall z,w C:
    abs(C_abs(z)-C_abs(w))<=C_abs(z-w)
```

- `ComplexReverseTriangle`：[独立tracer](../../../proof_nodes/atomic/by_builtin_rule/complex_reverse_triangle.lit)。
### LEG23

```litex
forall a,b Z*,m N+:
    m%abs(a)=0
    m%abs(b)=0
    =>:
        lcm(a,b)<=m
```

- `LcmCommonMultipleBound`：[独立tracer](../../../proof_nodes/atomic/by_builtin_rule/lcm_common_multiple_bound.lit)。
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

- `CartReconstruction`：[独立tracer](../../../proof_nodes/equal/by_builtin_rule/cart_reconstruction.lit)。
### LEG33

```litex
forall a,b N:
    a<=b
    =>:
        finite_set_size(range(a,b))=b-a
```

- `RangeSize`：[独立tracer](../../../proof_nodes/equal/by_builtin_rule/range_size.lit)。
- `ClosedRangeSize`：[独立tracer](../../../proof_nodes/equal/by_builtin_rule/closed_range_size.lit)。

## 实现与边界

- 换指标：有限乘积保留实际双射的VerifyFactResult。无序reduce还保留operation和seed匹配；它的总齐次二元signature守卫保证整体WD已检查结合律与交换律。函数复合匹配使用实际绑定ID和alpha结构，外层同名/其它变量不能冒充局部index。
- 不交并拆分：修正原aggregate partition owner。限制函数整体定义域不同，不能强求全局函数相等。优先识别相同函数或精确字面restriction；保留已检whole-function equality路线，其他情况仍给实际逐点proof。相同修正覆盖该owner的有限乘积拆分，不改变区间分拆。语义前提均留在payload，逐点分支保留closed local_env；直接字面restriction依赖整体WD，不重新开启更强搜索权限。
- 有限和三角界：匹配同一有限域的 `abs(sum)` 与精确逐项abs的literal callback；实数和/函数体载体由整体WD证明。任意h、其它domain、外层捕获值、去掉abs或复数混入不冒充该式。
- 索引并集：索引有限性为实际VerifyFactResult；各项有限性直接匹配完整已存forall证书，保留FactId和source/target参数renaming。带额外guard或另一family的证书不能替换。未开启任意forall实例化搜索。
- 其余八类使用专有成功proof payload保留需要的域、序、分解、整除、维数与逐factor证据。Complex modulus的两种triangle为整体WD后的结构规则。
- 未修改Stmt/Obj/Fact AST、Env/Runtime字段与状态合同、全局搜索预算或权限；未加trust，未提交或发布。原8类和本次5类一起完成当前scope的持久验收。

## 复现与回执

`cargo build --release --offline --lib --bin litex`；随后按各tracer注释执行 `target/release/litex -strict -f <file>`。Rust选择 `thirteen_builtin_rules`、`finite_set_reindex`、`legacy_small_capability_repair_tests`、`legacy_next_capabilities`、`legacy_final_capabilities`、`aggregate_`、`finite_set_reduce_singleton`、`rule_language_methods`、`acceptance_equality_named_language_methods`，每组实际非零选择。

机器证据：[完成journal](../../proof_journals/thirteen_builtin_rules_2026-10-05.json)。历史before source、binary、原stdout/JSON、最终source/binary、命令与tests回执保留在配套内容寻址包；缓存不归档。

遇到的流程修正也保留：第一版针对性测试误用非等式WD入口检查EqualFact，正确返回InternalBug；测试改为合法入口后通过。首个focused filter `legacy_small_capabilities` 选0项，没有视为成功；实际库存名为 `legacy_small_capability_repair_tests`，纠正后13/13通过。首次partition逐点检查因restricted WD重查carrier失败，改从已经通过整体WD的精确restriction结构消费；一般逐点分支仍保留实证和作用域。

## 扫描期间另一个共享更新的复验：SH10

本任务没有修改ODE文件。首次扫描仍在 `abs(slope1-slope2)>0` 失败；收尾检测到其mtime更新后，重新运行最新完整源文件，而非沿用旧输出。更新后的[完整ODE入口](../../../../showcases/math_concepts_in_litex/12_ordinary_differential_equations_in_nutshell/main.lit) strict exit0 / root success true，执行前后SHA256均为 `30c6fcf1c2c31e4df4548a5617aedc5968b6120ff8afa625ce485b899dd23815`。

该处现在有实际显式证明（全文件还包含其它桥）：

```litex
claim:
    ? abs(slope1-slope2)>0
    by contra:
        ? abs(slope1-slope2)>0
        abs(slope1-slope2)<=0
        0<=abs(slope1-slope2)
        abs(slope1-slope2)=0
        abs(slope1-slope2)!=0
        impossible abs(slope1-slope2)=0
```

上面的块依赖完整函数中已有 `slope1-slope2!=0`，不是无上下文独立正例。当前完整入口通过后，SH10移出具体活动纠错记录；旧失败原回执保留历史身份。最新剩余卡因此为25而非26。复现命令：`target/release/litex -strict -f showcases/math_concepts_in_litex/12_ordinary_differential_equations_in_nutshell/main.lit`。
