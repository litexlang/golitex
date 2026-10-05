# Native factorial / gcd / lcm migration record — 2026-10-05

Open local candidates (canonical status belongs to plan/src收尾总清单.md):

```litex
forall m,n N:
    m<=n
    =>:
        factorial(m)<=factorial(n)
forall m N+,n N:
    m<n
    =>:
        factorial(m)<factorial(n)
forall a,b Z*:
    lcm(a,b)%abs(a)=0
```

Legacy passes allthree; current WD passes then truth search misses. LEG39 groups strict/weak/direction forms, preserving positive smaller argument because `factorial(0)=factorial(1)=1`; LEG40 groups both abs-input divisors. No kernel implementation in this audit. Wrongstrict0!/1!, reversedorder, unrelatedlcm divisor and invalid domain remain rejected. Current lcm total zero domain and partial gcd domain stay unchanged.

Solved author route / optional AU59:

```litex
claim:
    ? forall n N+:
        factorial(n)=n*factorial(n-1)
    n-1 $in N
    (n-1)+1=n
    factorial(n)=factorial((n-1)+1)
    factorial((n-1)+1)=((n-1)+1)*factorial(n-1)
    ((n-1)+1)*factorial(n-1)=n*factorial(n-1)
    factorial(n)=factorial((n-1)+1)=((n-1)+1)*factorial(n-1)=n*factorial(n-1)
forall n N+:
    factorial(n)=n*factorial(n-1)
```

This whole source passes both versions and subsequent original theorem reuse passes in a fresh public Runtime. [Persistent source](../../../proof_nodes/equal/by_builtin_rule/factorial_predecessor_from_successor.lit).

Solved nonzero/WD route / optional AU60:

```litex
claim:
    ? forall n N:
        factorial(n)!=0
    0<factorial(n)
    factorial(n)!=0
forall n N:
    factorial(n)!=0
forall m,n N:
    m<=n
    =>:
        factorial(n)%factorial(m)=0
```

Whole original natural domain and remainder target preserved, no trust/new assumption. [Persistent source](../../../proof_nodes/equal/by_builtin_rule/factorial_divisibility_from_positive.lit) passes. Bare nonzero fails at search; baredivisibility earlier at factorial(m)!=0 WD. Existing LEG18 with carrier premises remains passed/closed; do not reopen its builtin implementation. Positivity or membership first both work. False claims fail and correct theorem remains reusable, ordinary Runtime does not claim whole-try rollback.

`!=` remains a single token; spacedfactorial equality and parenthesized postfix pass current, four old ParseErrors are syntax observations, not mathematical regressions. Current Z* gcd/symmetry/zero and lcm idempotent/productreverse improve over selected old inputs. Neutraltrue unsupported formulas are separately classified in the report.

[Full report with86 complete sources](../../../../plan/迁移的plan/legacy-factorial-gcd-lcm-audit-2026-10-05.md), [full raw journal](../../../../plan/迁移的plan/proof_journals/legacy-factorial-gcd-lcm-audit-2026-10-05.json), [owner coverage](../../../../plan/迁移的plan/proof_journals/legacy-factorial-gcd-lcm-owner-coverage-2026-10-05.json).172normalstrict-e/86Detailed/4Runtime101frames0errors/11files7pass4expectedreject.16receipt-provenancechecks, not kerneltests. Frozen154f7995/2428079e660src/Cargo stable; only2newauthor examples plus docs, no Rust/AST/Env/Runtime/search/domain edits. Canonical68/460 remains selected exactnamed hits, not allbranch/independentreplay completion.
