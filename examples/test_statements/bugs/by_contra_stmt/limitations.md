# ByContraStmt: remaining all-fact feature work

Task: any Fact as a contradiction target or closing fact, 2026-10-02/03.
Scope: golitex / classified logical negations. Unified NotFact and generic
not-block syntax were explicitly rejected by the maintainer.

Existing Atomic, Exist/NotExist, ExistUnique, And/Or/Chain, QF Forall,
QF ForallIff and NotForall constructors are implemented and tested using
unchanged Fact shapes. Unique and iff no longer belong to the missing
constructor list. See the [accepted quantifier experience](../../experience/problem_notes/by-contra-classified-quantifier-goals.md).

The closing-field change was explicitly authorized on 2026-10-03 and is now
implemented. It is no longer an open representation proposal; accepted controlled gates
are recorded in the [compound-closing acceptance note](../../experience/problem_notes/by-contra-compound-closing.md).
The ten existing Fact variants and their payload definitions are unchanged.

## Quantified premises and existential forall/iff clauses

```litex
by contra:
    ? forall x {0}:
        exist y {0} st {y = x}
    impossible 0 = 0
```

This reverse-assumption construction remains rejected. Its logical opposite
requires an existential counterexample with a universal condition:
∃x∈{0}, ∀y∈{0}, y≠x. NotForall.then_facts and PlainExistFact.facts are both
QF-only, so the existing payloads cannot store that nested formula. Quantified
iff sides or premises encounter the same boundary. This requires a concrete
classified representation/proof-evidence discussion; dropping a quantifier,
weakening WD, inventing a helper predicate or reintroducing generic NotFact
is not a repair.

## Flat Boolean representation cost

One flat Or-of-And Fact may require exponentially many branches when negating
an Or of many conjunctions. Existential body vectors can use a compact CNF
or DNF; the implementation estimates literal footprints and retains the
legacy shape on ties. Direct negation avoids an unnecessary CNF/DNF roundtrip,
and the iff constructor builds its counterexample clauses directly. Focused
stress controls exercise eight disjunctive premises without runaway expansion.
A future multiple-assumption certificate or new dedicated classified shape
changes a shared representation contract and requires discussion. No arbitrary
input cutoff was silently introduced.

## Accepted explicit atomic proof

The squared-i example is closed under the maintainer's accepted authoring
contract: provide `i * i = 0 * 0 = 0` before `impossible i * i != 0`.
The [current solution and 30-process acceptance](../../../test_objs/experience/problem_notes/imaginary_contra_explicit_chain_2026-10-04.md)
preserve the same goal and contradiction tail. The shorter automatic route
was not changed; its [dated nondeterminism evidence](atomic_i_nondeterminism_2026-10-03.md)
is historical capability evidence, not a pending Rust repair request.

[Plan and exact field proposal](../../../../plan/迁移的plan/by-contra-all-facts.md).
