# HaveFnByInducStmt: current proof-search capability

## Task context

- Task: explicit user correction of K003 on 2026-10-02.
- Scope: authoring recursive equality proofs.
- Related workspace: golitex.

K003 is a capability limitation, not an open bug. The former direct final assertion `f(2) = 0` was not found by automatic proof search in the captured baseline. The supported proof supplies the intermediate equalities:

```litex
have fn f(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: f(n - 1)
f(0) = 0
f(1) = 0
f(2) = f(2 - 1) = f(1) = 0
```

Verified source: [recursive-equation-explicit-chain.lit](../../boundaries/recursive-equation-explicit-chain.lit).

Decision, prior evidence, and verification commands: [K003 experience record](../../experience/problem_notes/K003-explicit-recursive-equation-chain.md).

K004 uses the same explicit-proof principle for an incrementing function:

```litex
have fn f(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: f(n - 1) + 1
f(0) = 0
f(1 - 1) = f(0) = 0
f(1) = f(1 - 1) + 1 = 0 + 1 = 1
```

Verified source: [recursive-increment-explicit-chain.lit](../../boundaries/recursive-increment-explicit-chain.lit). User decision and baseline proof: [K004 experience record](../../experience/problem_notes/K004-explicit-recursive-increment-chain.md).

Back to [statement folder](README.md) or [issue index](../README.md).
