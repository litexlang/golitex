# 非负主平方根乘积／商局部强化 — 2026-10-05

原式与专用tracer：

```litex
forall a,b R:
    0<=a
    0<=b
    =>:
        sqrt(a*b)=sqrt(a)*sqrt(b)
```

```litex
forall a,b R:
    0<=a
    0<b
    =>:
        sqrt(a/b)=sqrt(a)/sqrt(b)
```

修改前旧过／新WD后truth miss；两个当前叶原先要严格positive。现有Manual和十语言说明已有nonnegative合同。wave2局部prioritize checked nonnegative，再读取checked strongerpositive保存原路；商分母始终positive。existing两项实际proof、state/ceiling/AST/Env/Runtime/对象域不变。只有wave2 Rust文件改变。

专用 [principal_root_nonnegative_algebra.lit](../../equal/by_builtin_rule/principal_root_nonnegative_algebra.lit)前strict拒，最终strict过。六focused tests检真实requirements/citations、positive/reverse/zero、false/非法domain、搜索等级与失败不发布。首轮pureweak替换丢positive route和不成立的ceiling准备条件两失败保留；final6pass。79源/237strict-e/147Detailed、6Runtime172frames0errors0queued，final661source/Cargo稳定d6fde6e5/2cdf0fd2；未跑全release/Lean/replay，L2局部族无共享IR/schema变化。

已知平方0<=到>=显式衔接、参数alias root链属于AU08；positive integer power carrier/间接等式属于AU63，都有当前完整proof，正式BT27>=源仍过，不重开。

[全部原源/作者/控制与构建限制](../../../../plan/迁移的plan/legacy-root-power-consumers-audit-2026-10-05.md)、[fullraw](../../../../plan/迁移的plan/proof_journals/legacy-root-power-consumers-audit-2026-10-05.json)。
