# Nested modulo integer guard — solved 2026-10-05

Original false source:

```litex
(3%((1/2)*4))%4=3%4
```

Legacy rejected, baseline current accepted: left=1/right=3. All enclosing modulo WD was satisfied; the actual winner `ModNestedDivisibleAbsorption` only matched an inner product containing the outer modulus. Product integrality does not imply multiplier integrality. The reverse product, typed alias and arbitrary real multiplier universal shared the same defect.

The pure matcher now returns the multiplier. Its local verifier checks `multiplier $in Z` with the inherited builtin-premise state and retains the successful result in `proof_of_requirement_facts`. Detailed recursively projects that real evidence; the explicit-integer input cites its actual stored dom fact f1. No fresh state, expanded search ceiling, AST, Env/Runtime or modulo-domain change.

```litex
forall a Z,k R,m N+:
    k $in Z
    k*m $in N+
    =>:
        (a%(k*m))%m=a%m
forall a Z,k,m Z*:
    (a%(k*m))%m=a%m
(3%((-2)*4))%4=3%4
```

These whole current sources pass. Mod permits nonzero signed integer moduli; quot separately requires positive integer divisors. Initial negative-inner draft classification was mistaken, and the original raw record is preserved with an analytical correction.

The persistent [tracer](../../equal/by_builtin_rule/nested_mod_integer_multiple.lit) passes as the first direct strict-file gate after both post/final builds. Five local tests cover valid/false cases, exact stored integer premise, search ceiling and failed-publication reuse. Nine Detailed plus two locale consumer tests also pass: final16 selected, not all kernel tests. The first ceiling test had omitted enclosing WD preparation; corrected test context and successful recheck are retained without changing the production fix.

One public Runtime previously accepted false source, correct value equalities and subsequent `1=3`; final rejects false source and `1=3`, continues to accept the valid theorem, then rejects repeats. Ordinary failed-source feedback is not whole-try rollback. Source declarations can persist, so a separate alias-shadowing ParseError and its one unexecuted queue entry are recorded independently.

[Full categorized report](../../../../plan/迁移的plan/legacy-modular-quotient-audit-2026-10-05.md) includes58 complete cold inputs,227normal strict-e,167Detailed,24strict-file gates and8Runtime/188actualframes. [Full raw journal](../../../../plan/迁移的plan/proof_journals/legacy-modular-quotient-audit-2026-10-05.json) preserves build/source/test/failed-attempt evidence. Final CLI154f7995/rlib2428079e,660src/Cargo stable; source delta only local producer, Detailed consumer and existing static localization fixture. No full release or independent citation replay claim.
