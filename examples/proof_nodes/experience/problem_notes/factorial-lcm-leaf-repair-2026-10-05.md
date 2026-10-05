# Factorial/lcm local leaves and positive integer spelling — 2026-10-05

LEG39/LEG40 are closed within their existing natural/integer/nonzero contracts:

```litex
forall m N+,n N:
    m<n
    =>:
        factorial(m)<factorial(n)
```

```litex
forall a,b Z*:
    lcm(a,b)%abs(a)=0
```

Factorial weak/strict payloads retain actual order and positive-smaller checks;
reverse-written source orders are checked directly under the inherited ceiling.
Lcm left/right abs-input identities remain separate leaves. Enclosing equality
WD retains integer and nonzero-modulus evidence; the other input may be zero.
No source premise is fabricated for the unconditional checked-domain identity.

AU68 is an optional spelling shortcut, not missing mathematical checkability:

```litex
claim:
    ? forall x N:
        0<x
        =>:
            x $in N+
    x>0
    x $in N+

forall x N:
    0<x
    =>:
        x $in N+
```

The same current full author already passed before repair. The existing
positive-integer owner now tries actual 0<x after x>0 at the same level,
retaining its existing integer_proof/positive_proof. The full factorial domain
refinement originally failed first at m in N+, not at its later factorial goal.

```litex
claim:
    ? forall m,n N:
        m<=n
        =>:
            factorial(factorial(m))<=factorial(factorial(n))
    factorial(m)<=factorial(n)
    factorial(factorial(m))<=factorial(factorial(n))

forall m,n N:
    m<=n
    =>:
        factorial(factorial(m))<=factorial(factorial(n))
```

The nested original short still fails cold. This complete original-target
author and exact reuse pass; no recursive search permission is raised. One
warm main result uses a real earlier published factorial forall with citation.
The N+/Z+ lcm shorts passed current WD before repair; their legacy failures
were earlier modulus WD failures, so they are not eight old regressions.

[Factorial tracer](../../atomic/by_builtin_rule/factorial_monotonicity.lit),
[lcm tracer](../../equal/by_builtin_rule/lcm_input_divisibility.lit), and
[complete author tracer](../../atomic/by_builtin_rule/factorial_order_author_routes.lit)
all pass current and legacy whole strict files. 76 cold sources/380calls,
21 false or WD-invalid controls remain rejected, 7Runtime168frames,
23 distinct focused Rust tests pass. Remaining LEG41/42/45 eight originals
freshly still oldpass/currentmiss; no repair is claimed for those.

17 owned Rust paths, 7 independent shared source changes separately retained;
final source/Cargo664 stable. No protected AST, Env/Runtime, state/domain,
search ceiling or compiler changes owned here; no full release or independent
proof replay gate. Broad migration goal remains active.

[Full report](../../../../plan/迁移的plan/legacy-factorial-lcm-leaf-repair-2026-10-05.md)
and [raw journal](../../../../plan/迁移的plan/proof_journals/legacy-factorial-lcm-leaf-repair-2026-10-05.json).
