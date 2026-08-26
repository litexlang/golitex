# Transparent `let` acceptance: probability evidence intersections

- Target: `16_probability_theory/main.lit`, theorem
  `index_union_evidence_intersections`.
- Accepted change: bind
  `\evidence_intersection_sequence<Omega, events, probability, evidence, family>`
  once as `eis` and use `eis(idx)` in direct proof equalities.
- Preserved boundary: the exported theorem statement, existential source and
  witness facts, and canonical proof-evidence spelling remain expanded. An
  alias in `obtain ... from` was rejected because that position consumes a
  stored fact, rather than merely resolving an object.
- Evidence: the source-order replay and clean registered runner both completed
  with `ok: true`; see
  `16_probability_theory/.drafts/proof_journals/transparent_let_evidence_intersection_2026_08_26.json`.
- Trust delta: zero. This showcase is already the public artifact, so no mirror
  synchronization was required.

