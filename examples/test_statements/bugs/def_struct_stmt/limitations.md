# DefStructStmt: current boundaries

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: DefStructStmt restriction and tooling observations.
- Related workspace: golitex.

These boundary notes are separate from the original K-number issue groups.
The dated observations below distinguish restrictions from unresolved semantics.

### Input: `struct Single:` with only `x R`

- Observed boundary: Parse error: `struct definition expects at least two fields`.
- Supported route: Two-field plain and parametric structs.
- Existing reproductions: [single-field-is-currently-unsupported.lit](../../negative/def_struct_stmt/single-field-is-currently-unsupported.lit).

Malformed initial attempts and unsupported shorthand remain in the chronological journal; they are not silently promoted to confirmed bugs.

## Unused parameter test expectation — closed 2026-10-05

The maintainer confirmed the old negative was wrong: K absent from the fields
does not distinguish Point<N,R> from Point<Z,R>. The exact old template call
and its reverse are now executable positives. Actual value-carrier, tag-carrier,
wrong-object and missing-guard negatives remain checked. Struct semantics and
production proof search are unchanged.

The current release Rust gate passes 955/955 lib tests and 1/1 integration test;
the surrounding module passes 7/7. Concrete pending paragraphs were removed.
[Solution and raw evidence](../../experience/problem_notes/unused-struct-parameter-test-cleanup-2026-10-05.md).
[Closed DEC04](../../../../plan/src收尾总清单.md#dec04).

Back to [issue index](../README.md).

## Historical serious-bug audit — 2026-10-05

The earlier 933/934 snapshot and its stale expectation are preserved in the
[frozen consolidated acceptance](../../../../tests/tooling/acceptance/conversation-serious-bug-audit-2026-10-05.md).
It is not the current test status; the cleanup above supplies the current gate.
