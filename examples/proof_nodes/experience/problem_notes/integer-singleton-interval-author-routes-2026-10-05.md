# Integer singleton interval author routes — 2026-10-05

The old fixed singleton rule accepts these full goals; current WD succeeds
before the equality search misses:

```litex
forall x,n Z:
    n<=x
    x<n+1
    =>:
        x=n
```

```litex
forall x,n Z:
    n<x
    x<=n+1
    =>:
        x=n+1
```

Existing local integer adjacency/successor proves the missing weak bound,
then known-bound antisymmetry proves the original equality:

```litex
claim:
    ? forall x,n Z:
        n<=x
        x<n+1
        =>:
            x=n
    x<=n
    x=n

forall x,n Z:
    n<=x
    x<n+1
    =>:
        x=n
```

```litex
claim:
    ? forall x,n Z:
        n<x
        x<=n+1
        =>:
            x=n+1
    n+1<=x
    x=n+1

forall x,n Z:
    n<x
    x<=n+1
    =>:
        x=n+1
```

Seventeen legacy-positive singleton shorts have checked complete same-target
current proofs, grouped as optional AU65. No new mathematical capability,
kernel leaf, AST/result/Env/Runtime/state/search/domain mutation is claimed.
For inverse strict premises, explicitly publish x<n+1 or n<x first; the first
failed routes are retained. Antisymmetry intentionally only cites known weak
bounds to avoid recursive equality search. Do not expand its recursion.

```litex
claim:
    ? forall x,n Z:
        x>=n
        n+1>x
        =>:
            x=n
    x<n+1
    x<=n
    x=n

forall x,n Z:
    x>=n
    n+1>x
    =>:
        x=n
```

The [nine complete author proofs](../../equal/by_builtin_rule/integer_singleton_interval_author_routes.lit)
and exact original reuse pass whole strict files in both versions. Real-domain,
missing-bound, two-point closed intervals, wrong endpoint/jump and three false
author controls reject. Existing AU44 source orientation is not a new bug.

83 complete cold sources/166 recorded normal strict-e/83 Detailed; 4 persistent
Runtime sessions98 actualframes0errors/queued. Three warm accepts depend on
earlier valid universals and are separated from cold results. Lifecycle15
checks publication/reuse with false goals still rejected. Twelve current
strictfile calls8pass4false rejects; two legacy strictfilespass. No Rust tests,
full release, all-language or independent replay claims. One initial legacy
leading-negative CLI error raw is missing; only its forensic repetition is
stored, and exact same source legacy strict-f passes. It is not math rejection.

CLI45a90bedd20f6b4e2bf2edb0ea869ffa9449726a5943bed02231641cd356e5b6,
rlib48f771608b8f68595b3a9ea3980a9ab7df68ea467d4703cd81c865fc17e67409;
661条src/Cargo构建、probe与记录末稳定. Root113/legacy32 unchanged, AU65 added under AUTH02.
[Complete report](../../../../plan/迁移的plan/legacy-integer-adjacency-audit-2026-10-05.md)
and [full raw journal](../../../../plan/迁移的plan/proof_journals/legacy-integer-adjacency-audit-2026-10-05.json)
preserve all complete sources, failed attempts, emitted branch tokens and gates.
