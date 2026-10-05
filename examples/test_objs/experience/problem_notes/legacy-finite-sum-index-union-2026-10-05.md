# 已解决记录：有限聚合与索引并集 — 2026-10-05

原目标已经在冻结 current84d13156 strict验证；共享实现非本审计实施。只记录实际原例、近邻控制和完整作者证据，不代替全量发布门。

## LEG12：有限乘积沿已证双射换指标

```litex
forall X,Y finite_set,g fn(y Y)X,f fn(x X)R:
    $bijective(Y,X,g)
    =>:
        finite_set_product(X,f)=finite_set_product(Y,fn(y Y)R {f(g(y))})
```

最新 Normal/Detailed/所选反馈通过，实际规则 FiniteSetProductReindex；前提及错误输入控制见专项报告。

## LEG13：无序 reduce 沿已证双射换指标

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

最新 Normal/Detailed/所选反馈通过，实际规则 FiniteSetReduceReindex；前提及错误输入控制见专项报告。

## LEG14：有限和按不交并拆分

```litex
forall A,B finite_set,f fn(x union(A,B))R:
    intersect(A,B)={}
    =>:
        finite_set_sum(union(A,B),f)=finite_set_sum(A,fn(x A)R {f(x)})+finite_set_sum(B,fn(x B)R {f(x)})
```

最新 Normal/Detailed/所选反馈通过，实际规则 FiniteSetSumDisjointUnion；前提及错误输入控制见专项报告。

## LEG22：有限和的绝对值三角界

```litex
forall S finite_set,f fn(x S)R:
    abs(finite_set_sum(S,f))<=finite_set_sum(S,fn(x S)R {abs(f(x))})
```

最新 Normal/Detailed/所选反馈通过，实际规则 FiniteSetSumTriangle；前提及错误输入控制见专项报告。

## LEG32：有限索引且逐项有限的并集有限

```litex
forall I nonempty_set,X set,A fn(idx I)power_set(X):
    $is_finite_set(I)
    forall k I:
        $is_finite_set(A(k))
    =>:
        $is_finite_set(index_union(I,X,A))
```

最新 Normal/Detailed/所选反馈通过，实际规则 FiniteIndexUnion；前提及错误输入控制见专项报告。

## 保留完整作者路线

```litex
thm real_finite_scale_into_complex:
    ? forall T finite_set,c C,G fn(k T)R:
        finite_set_sum(T,fn(k T)C {c*G(k)})=c*finite_set_sum(T,G)
thm real_abs_from_negative_double_bound:
    ? forall x,y R:
        x<=y
        -x<=y
        =>:
            abs(x)<=y
    0-x=-x
    0-x<=y
claim:
    ? forall S finite_set,f fn(x S)R:
        abs(finite_set_sum(S,f))<=finite_set_sum(S,fn(x S)R {abs(f(x))})
    claim:
        ? forall k S:
            -f(k)<=abs(f(k))
        -f(k)<=abs(-f(k))
        abs(-f(k))=abs(f(k))
    release thm finite_set_sum_le_from_pointwise(finite_set_sum(S,f),finite_set_sum(S,fn(k S)R {abs(f(k))}))
    release thm finite_set_sum_le_from_pointwise(finite_set_sum(S,fn(k S)R {-f(k)}),finite_set_sum(S,fn(k S)R {abs(f(k))}))
    release thm real_finite_scale_into_complex(S,-1,f)
    release thm finite_set_sum_substitution(finite_set_sum(S,fn(k S)R {-f(k)}),finite_set_sum(S,fn(k S)C {(-1)*f(k)}))
    finite_set_sum(S,fn(k S)R {-f(k)})=finite_set_sum(S,fn(k S)C {(-1)*f(k)})=(-1)*finite_set_sum(S,f)=-finite_set_sum(S,f)
    release thm real_abs_from_negative_double_bound(finite_set_sum(S,f),finite_set_sum(S,fn(k S)R {abs(f(k))}))
```

在原生补齐前，这份同目标原域全文已固定旧版/当前两版通过；没有 trust 或新增假设。

[完整审计报告](../../../../plan/迁移的plan/legacy-finite-sum-index-union-audit-2026-10-05.md)；[完整命令及 raw](../../../../plan/迁移的plan/proof_journals/legacy-finite-sum-index-union-audit-2026-10-05.json)。
