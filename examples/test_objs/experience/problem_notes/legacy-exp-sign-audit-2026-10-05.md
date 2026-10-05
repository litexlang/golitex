# exp／ln／sign周边对照与作者路线 — 2026-10-05

本轮kernel只读；六份持久作者proof已strict过。两个新局部候选未实施：

```litex
forall a,b R:
    a<b
    =>:
        exp(a)<exp(b)
```

```litex
forall a,b R+:
    ln(a)<=ln(b)
    =>:
        a<=b
```

```litex
1<e
e!=1
forall x R+:
    ln(x)=log(e,x)
```

```litex
e $in R+
0<e
e!=0
forall x Z:
    exp(x)=e^x
```

LEG41所选原式旧过／新WD后truth miss，LEG42两个guard完整前缀过／最终EQ miss。实指数e^x R域仍DEC05未决，不称刻意删除或直接放宽。详见 [完整107对照与全部作者代码](../../../../plan/迁移的plan/legacy-exp-sign-audit-2026-10-05.md)。

现有路线省去必修误报：exp/ln用逆函数证单射；exp差用已证nonzero instance、sum与cancel；ln积／商先显式证positive instance再用exp单射。sign用magnitude做zero/nonzero，claim+atomic contra做反向；按x<0/x=0/x>0的case加显式0实carrier与0<x实例证明bounds/weak monotone。strict sign和order reflection是错误目标，不能搬。

六持久完整source：[单射](../../../proof_nodes/equal/by_builtin_rule/native_exp_ln_injectivity.lit)、[指数差](../../../proof_nodes/equal/by_builtin_rule/native_exp_difference_from_sum.lit)、[ln乘积](../../../proof_nodes/equal/by_builtin_rule/native_ln_product_from_exp.lit)、[ln商](../../../proof_nodes/equal/by_builtin_rule/native_ln_quotient_from_exp.lit)、[sign零非零](../../../proof_nodes/equal/by_builtin_rule/sign_zero_nonzero_from_magnitude.lit)、[sign弱order](../../../proof_nodes/equal/by_builtin_rule/sign_order_from_cases.lit)。这些作者例子没有新数学假设或trust，最后均可复用原裸目标。

107不同cold/321strict-e/214Detailed、14Runtime288frames0errors0unexecuted、32strictfiles18过14按分类拒；6shared source漂移保存后重建，latest3e77bbdd/4b142a1a构建稳定，两current截面接受一致；probe末又2source漂移，latest live HEAD未验，无本审计kernel修改。canonical71/460是actualnamed receipt覆盖，不是全部分支或独立replay。完整raw：[journal](../../../../plan/迁移的plan/proof_journals/legacy-exp-sign-audit-2026-10-05.json)。
