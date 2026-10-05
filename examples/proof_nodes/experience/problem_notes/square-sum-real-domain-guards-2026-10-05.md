# 两个平方和前向叶的实数域守卫 — 2026-10-05

旧版正确拒绝、新版before接受的原反例：

```litex
forall a,b C:
    a^2+b^2=0
    =>:
        a=0
```

```litex
forall a,b C:
    a!=0
    =>:
        a^2+b^2!=0
```

a=1,b=i让平方和为0，却有a!=0。Current Pow/Add WD允许C，不能推出real平方非负。zero leaf原只有graph形状；nonzero leaf原只有component非零。final两叶先真实检查两base inR，zero还保留sum=0实际路径，nonzero保留component proof；相应Detailed消费三项证据。只改五Rust路径，未改AST/Env/Runtime/state/ceiling/WD域/ABI。

[persistent guard tracer](../../equal/by_builtin_rule/square_sum_zero_real_guard.lit)含real/signed-carrier/multiply/alias、C显式R及合法C反向OR；[OR完整作者](../../atomic/by_builtin_rule/square_sum_nonzero_from_cases.lit)保持原real目标，普通cases后两版都过。短OR省写归AUTH02/AU42，不扩大通用搜索。

最终7族tests+9Detailed+1locale通过；87distinct输入/397strict-e/307Detailed，12Runtime365frames0errors0queued，22false源从接受改拒，全部已有current合法通过保持。latest 8fabedc5583f70201d3a6d9852933899193d23ccdddf64e59cb1a7873fa2315a/f054fd62fb200ed2589f2256ba12dc52435f775fddae142f9250ddf7b03f1a01，661src/Cargo构建内稳定，shared drift由record-end单列；无fullrelease/Lean/独立replay声明。

[完整原例与控制](../../../../plan/迁移的plan/legacy-square-sum-consumers-audit-2026-10-05.md)、[全raw](../../../../plan/迁移的plan/proof_journals/legacy-square-sum-consumers-audit-2026-10-05.json)。统一LEG44已闭，broad goal仍active。
