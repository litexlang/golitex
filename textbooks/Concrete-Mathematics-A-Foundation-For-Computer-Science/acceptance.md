# Publication acceptance

## Chapter 1 — Recurrent Problems

- Source: `todo_textbook_chapters/former_textbook/chapter01-recurrent-problems.lit`
- Current-release source baseline: exit 0, top-level `result:success`,
  `ok:true` (about 157 seconds).
- Maintained draft file gate: exit 0, top-level `ok:true`.
- Maintained draft dependency closure: exit 0, top-level `ok:true`.
- Trust delta: 0. The 29 existing executable trust markers are preserved.
- Persistent-session evidence: an exact outer-`try` replay of the complete
  chapter exceeded 300 seconds; a source-order replay then isolated the same
  behavior to the first `hanoi_moves` recursive definition, which emitted no
  block event within 210 seconds. This is recorded as a session transaction
  performance limitation, not a file-verification failure.

Canonical file and repository gates were rerun after materialization; both
exited 0 with top-level `result:success` and `ok:true`.
