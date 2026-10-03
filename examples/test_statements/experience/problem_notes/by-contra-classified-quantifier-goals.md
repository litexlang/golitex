# Classified quantifier targets for contradiction

Task: strengthen by-contra without unified NotFact, 2026-10-02/03.
Scope: existing Fact constructors, whole-formula semantics, binders and proof scope.
Ownership: category 2 local construction on unchanged AST/state APIs; shared
forall-iff goal parser alignment escalates validation to L4.

Unique existence is negated as a forall: every satisfying candidate has a distinct
satisfying alternative. Zero witnesses make this condition vacuous; exactly
one witness refutes it; several witnesses satisfy it. Second-candidate binders
are fresh, carriers are instantiated in source order and differing components
are joined by Or, not And. Real unique contra and finite 0/1/2-witness models,
dependent carriers and component controls pass.

Forall-iff with QF sides gets an existential counterexample under the original
domain: (not P or not Q) and (P or Q), where each side is its whole conjunction.
Distributing disjunction across conjunction vectors preserves compact existing
QF clauses; the constructor does not expand the entire equivalence into one
DNF. Shared goal parsing now accepts the already parsed ForallFactWithIff and
reopens its existing binders. False iff and malformed atomic multiline controls
reject. Sixteen independent Boolean assignments verify the complete equivalence.

NotForall with several conclusions negates the whole conjunction: at least one
conclusion fails. Counterexample construction chooses the smaller CNF/DNF
literal footprint; ties preserve legacy existential clause shape. Direct QF
negation avoids double expansion. Eight disjunctive premises and a many-clause
iff remain compact in the focused tests.

Stable tracers: [unique existence](../../../stmt_nodes/by/by_contra_unique_existence.lit),
[forall iff](../../../stmt_nodes/by/by_contra_forall_iff.lit), and
[classified goals](../../../stmt_nodes/by/by_contra_classified_goals.lit).
No Stmt/Fact fields, variants or Env/Runtime state changed. Reverse assumptions
and witness evidence remain local; only a checked target is published.

Final commands/hashes/results are in the [classified-goal acceptance receipt](../../proof_journals/by_contra_classified_acceptance_2026-10-03.json).
The full-kernel gate retains separate existing WD/projection failures;
passing the focused constructors does not imply all library gates are green.
[Unfinished all-fact closing/nested representation work](../../bugs/by_contra_stmt/limitations.md)
remains visible; impossible_fact still AtomicFact pending concrete authorization.
