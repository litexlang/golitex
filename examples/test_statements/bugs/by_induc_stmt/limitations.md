# ByInducStmt: automatic carrier evidence decision

## Task context

- Task: conversation closeout retest requested 2026-10-04.
- Scope: ordinary/strong induction goal WD and explicit checked type facts.
- Related workspace: golitex; canonical route OBJ10.

Label: `kernel_problem`; classification: category 1 authoring route is verified,
automatic category 2 behavior remains a shared WD/evidence decision.

```litex
have fn f(x N) N = x
by induc n from 0:
    ? f(n) = f(n)
```

The unchanged positive Rust expectation currently fails at step goal WD:
`f(n + 1)` requires `n + 1 $in N`. The induction domain provides integer and
lower-bound evidence, but the Direct structural Add route does not obtain a
stored natural-number fact from that combination. This is not a false goal.

The authoring route keeps the same goal and adds a checked fact:

```litex
have fn f(x N) N = x
by induc n from 0:
    ? f(n) = f(n)
    n $in N
```

Ordinary and strong variants pass. `from -1` and `n / n = 1` starting at zero
remain rejected. No trust or global search-level reset was added. The original
bare Rust test remains red rather than silently changing its expectation.

Decision: accept this explicit type-fact boundary, or require induction to
derive and expose checked domain/carrier evidence automatically. The latter
needs an agreed proof-evidence/WD contract before implementation. Owner:
maintainer decides; Codex implements the selected bounded path and verifies
bare/explicit, ordinary/strong, wrong-start and zero-division controls.

[Acceptance and raw controls](../../../../tests/tooling/acceptance/conversation-closeout-retest-2026-10-04.md#induction).
[Canonical OBJ10](../../../../plan/src收尾总清单.md#obj10).
