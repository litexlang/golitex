# First-quadrant rule acceptance and live-build limitation

Six dedicated leaves restore the real first-quadrant nonzero and tan/cot positivity contract from actual strict bounds. Former WD failure and current code are preserved in [the quadrant tracer](../../atomic/by_builtin_rule/trig_first_quadrant.lit); [quotient WD](../../equal/by_builtin_rule/trig_first_quadrant_quotient_wd.lit) also checks the unchanged partial-operation requirements.

```litex
# Before: old passed, current baseline rejected cos(x)!=0 during tan WD.
# forall x R:
#     0<x
#     x<pi/2
#     =>:
#         0<tan(x)
# Now: verified on the exact isolated baseline plus own rule overlay.
forall x R:
    0<x
    x<pi/2
    =>:
        0<tan(x)
```

The actual lower and upper known-premise proofs retain source IDs and comparison orientations. Two NZ and four Less/Greater positive rules each have a dedicated evidence struct and ten-language explanations. Parent WD retains real-argument and denominator proof. Existing larger-interval and known/congruence routes keep precedence. Bounds are not published and the caller's global state/search permissions are unchanged.

24 focused Rust tests, six strict files, one FAQ fence, six actual winning leaf/citation checks and two final source-reuse cycles pass **on the 703-file frozen baseline plus the 11-file own overlay (705 source/Cargo files)**. Four actual partial WD consumers retain the same two bound sources. There are68 independent cold sources,17 verdict improvements and20 rejected false/domain controls.

The square denominator has a further permission boundary. Its bare first-quadrant law still fails `cos(x)^2!=0` WD; publishing the verified base-NZ consequence first is checkable without adding an assumption:

```litex
forall x R:
    0<x
    x<pi/2
    =>:
        cos(x)!=0
        1+tan(x)^2=1/cos(x)^2
```

Do not put that bridge only into a claim proof body and assume it can repair earlier target WD; the actual claim probe still rejects before its body.

The live shared source changed `LaunchCommand::Extract` to `ExtractExecutableCode` while `Runtime::new` retains four old references. A real release build fails4E0599. This task preserves those shared/protected files and does not claim live combination acceptance. The root SOP remains active until the current API contract is completed and the recorded live gates can run. The [full report](../../../../plan/迁移的plan/legacy-trig-quadrant-order-followup-2026-10-06.md) retains the failure, isolated proof provenance, remaining negative-common-factor and original guarded tan/cot-order cards, and exact next checks.

Current acceptance supplement: shared Runtime launch initialization was independently completed. Actual current706 build/43tests/351pairs and full frozen708 final gates now pass; the former startup proposal is superseded, not approved or applied by this task. See [signed difference closure](signed-difference-order-2026-10-06.md) for actual live708 source-stable12 strict files/14public frames/5native output tests. Historical isolated evidence above remains unchanged.
