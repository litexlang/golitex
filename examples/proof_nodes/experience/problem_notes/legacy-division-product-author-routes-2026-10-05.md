# 乘除互转作者路线与复合分母边界 — 2026-10-05

原两方向旧过／current WD后search miss：

```litex
forall a,b,c R:
    b!=0
    a/b=c
    =>:
        a=c*b
```

```litex
forall a,b,c R:
    b!=0
    a=b*c
    =>:
        a/b=c
```

完整samegoal作者两版过：

```litex
claim:
    ? forall a,b,c R:
        b!=0
        a/b=c
        =>:
            a=c*b
    a=(a/b)*b=c*b

forall a,b,c R:
    b!=0
    a/b=c
    =>:
        a=c*b
```

```litex
claim:
    ? forall a,b,c R:
        b!=0
        a=b*c
        =>:
            a/b=c
    a/b=(b*c)/b=c

forall a,b,c R:
    b!=0
    a=b*c
    =>:
        a/b=c
```

74旧正短式已有完整当前原目标proof，归AU64可选便利；另8真短式两版均拒但full proof皆过，不算旧遗漏。[持久作者文件](../../equal/by_builtin_rule/division_product_explicit_author_routes.lit)13完整proof及exactreuse严格通过；Q/Z/C、隐含R+/R* NZ、负分母、alias与顺序都保留原条件。

复合分母尚未闭，LEG45：

```litex
forall a,b,c,d R:
    b!=0
    d!=0
    a/(b*d)=c
    =>:
        a=c*(b*d)
```

旧过／current premise与goal WD过后truth miss。R/C每域三完整proof尝试（直接cancel、拆div、命名divisor）均oldpass/currentfail，不宣称显式不可证明或已检通。建议有限source-equality证据leaf，必须真实引用source和Div WD、继承premise ceiling；不复制旧boolean known-equality证据，不改AST/Env/Runtime/global search或domain。

193distinct输入/386strict-e/193Detailed；6Runtime205实际帧0sessionerrors/queued，独立生命周期[F,F,T,T,F,T,T,F,F,F,T,T]中合法publication/reuse过、错factor/缺NZ/错shift保持拒。13strictfiles6pass、3false reject、4valid candidatefail；expected failures不是修复完成。原numeric_power_rules整文件过。无Rust修改或fullrelease/Lean/independent replay验收。

当前冻结CLI e9f4f30aeda0c91769498ed731ecdef7d0cd250970cb7a643b0b22b34526eee6 /rlib 7f59e10a84cbddde898af47e0ea82ac0b41e3dfd9f693f9419cdcfe0c381884d；构建内、探针结束及记录时661条src/Cargo指纹稳定。八个LEG39–42原源当前再次旧过／新miss，保持候选未实施与原数学域。完整代码/所有尝试/raw见[专项](../../../../plan/迁移的plan/legacy-division-products-audit-2026-10-05.md)、[journal](../../../../plan/迁移的plan/proof_journals/legacy-division-products-audit-2026-10-05.json)。广域goal继续active。
