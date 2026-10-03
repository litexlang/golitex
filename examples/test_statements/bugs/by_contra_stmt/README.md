# ByContraStmt

Task: strengthen classified contradiction proofs, requested on 2026-10-02.
Scope: golitex / `ByContraStmt` goals and `impossible` facts.

Primary fixture: [by_contra_stmt.lit](../../by_contra_stmt.lit).
New compound-goal tracer: [by_contra_classified_goals.lit](../../../stmt_nodes/by/by_contra_classified_goals.lit).

K005 is accepted and removed from open issues; its [solution](../../experience/problem_notes/K005-classified-negative-existence-contra.md) retains native and unit controls.
Existing classified goal routes are implemented without adding a unified
`NotFact`. Remaining feature boundaries and repair ownership are in
[limitations.md](limitations.md), with concrete sources. The [existing atomic nondeterminism](atomic_i_nondeterminism_2026-10-03.md) is recorded separately. These pending
all-fact feature items are separate from the historical K-number issue count.

Back to [issue index](../README.md).
