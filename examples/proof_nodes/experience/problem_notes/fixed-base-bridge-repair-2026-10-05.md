# Legal fixed-base bridges — 2026-10-05

Task provenance: ongoing broad legacy capability audit and delegated bounded local Rust repair.

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
forall n Z:
    exp(n)=e^n
```

Former exact failures commented/current active in [Ln tracer](../../equal/by_builtin_rule/ln_as_euler_log.lit) and [Exp tracer](../../equal/by_builtin_rule/exp_as_euler_integer_power.lit). Two distinct typed identities, same actual argument/literal Euler base, both equality directions. No searched child; enclosing equality retains all log/power and native object WD. New leaf last in existing dispatch, no search/state/domain widening; ten languages and Detailed real owner gates pass.

```litex
1<e
e!=1
claim:
    ? forall x R+:
        exp(log(e,x))=x
    ln(x)=log(e,x)
    exp(log(e,x))=exp(ln(x))
    exp(ln(x))=x
    exp(log(e,x))=x

forall x R+:
    exp(log(e,x))=x
```

[Complete author file](../../equal/by_builtin_rule/native_fixed_base_author_routes.lit) verifies five unchanged original goals plus exact reuse: two aliases, two composite inverses, and ln order via fixed-base log. Bare inverse shorts both versions still miss, aliases oldpass/currentmiss at differing phases; current explicit original authors now pass. General real exponent DEC05 remains WD-rejected. Conditional nested-ln comparison LEG29 remains pending after complete current-source revalidation, even though integer Euler-power Ln authors pass.

```litex
forall a,b,c,d R:
    b!=0
    d!=0
    a/(b*d)=c
    =>:
        a=c*(b*d)
```

LEG45 remains oldpositive/currentsearchmiss. Follow owner/source proof and whole nonzero divisor obligations, not a domain or storage redesign.

16focusedtests/669source stable;58completecold inputs290calls;13false/invalid controls;20currentstrictfiles16pass4reject;3legacywholefilespass. Initial own E0753 module placement compile failure and two public draft input errors retained; corrected7 completeRuntime sessions132frames all error-free, 9 total sessions221actualframes. No fullrelease/replay claim.

[Full report](../../../../plan/迁移的plan/legacy-fixed-base-bridge-repair-2026-10-05.md), [raw journal](../../../../plan/迁移的plan/proof_journals/legacy-fixed-base-bridge-repair-2026-10-05.json) and [owner](../../../../plan/迁移的plan/proof_journals/legacy-fixed-base-bridge-owner-coverage-2026-10-05.json) record actual acceptance commands, failures, source guards, valid prior forall citations and exact same-target routes. Temporary task SOP transfers after final artifact/hash/link gate; broad goal ledger persists.
