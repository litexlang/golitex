# Valid-base logarithm algebra acceptance

Task: close the four existing log algebra leaf acceptance tail after the explicit pause. Scope: product, quotient, reciprocal, integer argument power and their actual Detailed/Normal consumers.

```litex
# Before: legacy passed; current equality search only admitted the >1 base route.
# forall a,x,y R+:
#     a<1
#     =>:
#         log(a,x*y)=log(a,x)+log(a,y)
forall a,x,y R+:
    a<1
    =>:
        log(a,x*y)=log(a,x)+log(a,y)
```

This exact source now verifies in `log_product_valid_base.lit`; the quotient, reciprocal and argument-power companion tracers also pass. The four leaves retain named mandatory argument proofs and the selected `LogAlgebraBaseProof`: greater-than-one, positive/below-one, or positive/nonunit. Twelve actual Detailed leaf instances preserve all three choices; ten-language Runtime tests and EN/ZH source citations verify the producer/consumer contract.

The paused test compile failure used `contains(&"proof_of_requirement_facts".to_string())` for `Vec<&str>`. At resumption the shared tree already used `contains(&"proof_of_requirement_facts")`; no Rust edit was made in this tail. Fresh selected tests: 6 log-family, 1 bilingual equality fixture, 9 Detailed, 3 language methods, all passed. Restricted forall WD remains rejected at its actual inherited ceiling; root verification and actual stored-forall reuse pass.

Four source-order false/good/reuse/false cycles cite the newly published FactId and leave false goals rejected. Four direct frozen-release `-strict -f` gates pass. The 100-source cold rerun has Normal/Detailed parity, 77 accepted and all 16 false/domain controls rejected. The seven pending source cases remain in the manifest; x>0 to positive integer power under log WD is still pending, and general real exponents keep their unsettled contract.

[Acceptance and commands](../../../../plan/迁移的plan/legacy-log-algebra-tail-2026-10-06.md) and [actual receipts/owners/remaining inputs](../../../../plan/迁移的plan/proof_journals/legacy-log-algebra-tail-2026-10-06-manifest.json) distinguish previous implementation, current shared updates and this verification-only tail. No broader release, Lean or independent certificate replay is implied.
