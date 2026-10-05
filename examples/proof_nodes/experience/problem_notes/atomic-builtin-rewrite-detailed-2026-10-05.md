# Atomic builtin rewrite Detailed输出：局部修复 — 2026-10-05

原证明已通过，输出仅`{"type":"by_builtin_rewrite"}`。现读取已有enum与payload，保留原目标、实际cite及verified child；无新增证明规则或类型字段。

```litex
forall n N:
    n=16
    =>:
        $prime(n+1)
```

持久例：[closed_numeric_prime.lit](../../atomic/by_builtin_rewrite/closed_numeric_prime.lit)。新Rust测试在英文/中文比较cited ID与同一次dom事实的stored ID，并验证子节点判17为prime、n=8假目标拒绝。7 module tests过，91current接受与before一致；actual KnownEqualObj/FnUnfold亦观察，OrderDual所选例未获胜。

完整source before/after、snapshot与raw：[专项报告](../../../../plan/迁移的plan/legacy-number-theory-audit-2026-10-05.md) / [journal](../../../../plan/迁移的plan/proof_journals/legacy-number-theory-audit-2026-10-05.json)。完整replay及直接numeric resolved叶来源合同未由此关闭。
