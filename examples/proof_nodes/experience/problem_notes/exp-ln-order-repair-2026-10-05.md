# exp/ln bounded order leaves and nested-WD boundary — 2026-10-05

Task provenance: active broad legacy migration goal; delegated local BR/WD repair, protected state/AST changes excluded.

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

Former exact failures are comments in [aggregate tracer](../../atomic/by_builtin_rule/exp_ln_order.lit), current code active. Exp R and Ln R+ strict/weak forward/reflection own eight independent leaves and actual argument_order/image_order. Source directions retain real citations; same inherited premise ceiling prevents mutual builtin recursion. Detailed and ten languages consume the actual winning owners. Individual leaf tracers are in the same directory and listed in the proof_nodes README.

```litex
claim:
    ? forall a,b R:
        a<b
        =>:
            exp(a)<=exp(b)
    a<=b
    exp(a)<=exp(b)

forall a,b R:
    a<b
    =>:
        exp(a)<=exp(b)
```

[Author tracer](../../atomic/by_builtin_rule/exp_ln_order_author_routes.lit) contains fourteen complete original targets and exact reuse: four strict→weak, eight ln sign, nested exp and inverse exp. They pass after the foundational order repair; cold optional shortcuts stay distinguished.

```litex
forall x R+:
    1<x
    =>:
        ln(1)=0
        ln(1)<ln(x)
        0<ln(x)
        ln(x) $in R+

forall x R+:
    1<x
    =>:
        ln(ln(x)) $in R
```

[Carrier tracer](../../../wd/ln_positive_image_carrier.lit) succeeds, but a comparison consumer of the same checked helper still fails predicate-domain WD. The old accepted complete comparison author is retained below; acceptance means this unchanged source passes, not merely its root carrier:

```litex
forall x R+:
    1<x
    =>:
        ln(1)=0
        ln(1)<ln(x)
        0<ln(x)
        ln(x) $in R+

claim:
    ? forall a,b R+:
        1<a
        1<b
        a<b
        =>:
            ln(ln(a))<ln(ln(b))
    ln(1)=0
    ln(1)<ln(a)
    0<ln(a)
    ln(a) $in R+
    ln(1)<ln(b)
    0<ln(b)
    ln(b) $in R+
    ln(a)<ln(b)
    ln(ln(a))<ln(ln(b))

forall a,b R+:
    1<a
    1<b
    a<b
    =>:
        ln(ln(a))<ln(ln(b))
```

Provisional owner: verify_atomic_fact/verify_well_defined.rs caps generated predicate-domain requirements at inherited BuiltinRule. Requirement ln(ln(a)) inR rechecks object WD, then cannot use the positive-image KnownForall at that lower ceiling. Investigate consumption of already checked parameter evidence locally; do not increase shared VerifyState permissions or add hidden cache. If owner/result/state contract changes are required, present the concrete decision before implementing. Invalid nested ln without >1 thresholds continues to reject.

```litex
1<e
e!=1
forall x R+:
    ln(x)=log(e,x)
```

```litex
forall a,b,c,d R:
    b!=0
    d!=0
    a/(b*d)=c
    =>:
        a=c*(b*d)
```

LEG42/45 are still unimplemented local candidates: full guard prefixes and WD pass; equality truth search misses. Current exp/ln order repair does not settle real exponent DEC05.

Latest source667 stable:20distinct focused Rust tests;112 completecold sources/784calls,23negative controls;17Runtime372frames;54 current strictfilecalls40pass14reject;3legacywholefiles pass. First test oracle incorrectly required ten different language names and was corrected without production translation edits. Five independent shared equality changes required latest rebuild/full revalidation and are preserved separately. No state/AST/default-domain/search/compiler owned edit, no full-release/replay claim.

Acceptance commands: cargo test --release --offline exp_ln_order_tests; selected project_detailed and language selector filters captured in journal; target/release/litex -strict -f examples/proof_nodes/atomic/by_builtin_rule/exp_ln_order.lit; same strict-file mode for author and carrier tracers. Full exact commands, builds, original failures, actual winning leaves and citations are in the [report](../../../../plan/迁移的plan/legacy-exp-ln-order-repair-2026-10-05.md), [owner](../../../../plan/迁移的plan/proof_journals/legacy-exp-ln-order-owner-coverage-2026-10-05.json) and [raw journal](../../../../plan/迁移的plan/proof_journals/legacy-exp-ln-order-repair-2026-10-05.json).
