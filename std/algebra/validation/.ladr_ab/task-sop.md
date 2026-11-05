# LADR A–B std implementation and FTA dependency milestone

Status: active, scope confirmed 2026-10-31.

## Goal contract

- Deliver reusable std interfaces and proofs corresponding to A–B (1A–2C and 3A–3D), with existing capabilities audited and reused.
- Also include complete FTA 4.12 and actual necessary dependencies; do not silently select all later packages. Defer general volume, the full exercise corpus, textbook migration and new native interfaces.
- Keep all authored mathematical code, validation and API documentation under std; scope plans and item records remain in the requested experiments workspace.
- Preserve existing Field and VectorSpace shapes, public contracts and shared verification ownership. No trust, axioms, source-specific WD fallback, native change or protected-type edit.

## Current increment: source 1.28 and 1.32

- Existing: additive_inverse_exists_unique proves exactly one y with space.add(x,y)=space.zero.
- Missing value: vector_neg<K,F,V,space>(x), selected from that proved relation. Its defining property and uniqueness must be directly usable after import.
- Follow-up: vector_difference<K,F,V,space>(u,v)=space.add(u,vector_neg(v)); minus_one_times_vector identifies F.neg(F.one) scalar multiplication with the selected inverse.
- K is nonempty, F an existing Field<K>, V nonempty, and space an existing VectorSpace<K,F,V>. Do not restrict to finite dimensions or R/C.
- Proof spine: existing inverse unique existence -> selected value -> defining law -> scalar distributivity and zero scalar law -> inverse uniqueness -> minus-one identity.
- Tracer: compute negative real and complex coordinates, including the native zero-dimensional space; reuse the general theorem from an independent imported consumer. Reject false signs while retaining Session context.
- Source target: std/algebra/vector_space.lit. Consumer target: this directory's main.lit.

## Verification protocol

Use one pinned current-release executable to avoid concurrent release-build replacement. Keep one live Session loaded through the accepted vector_space prefix; submit and journal one statement at a time, retaining context after ordinary failure. Materialize coherent accepted checkpoints and run strict source/imported gates there. No whole-book, Cargo or Lean gate is required for this source-only increment.

## Acceptance

- [x] Generic selected inverse and its specification accepted.
- [x] Difference and minus-one theorem accepted without new assumptions.
- [x] Strict saved source and independent imported use accepted.
- [x] R/C, zero-dimensional and refusal/use checks accepted.
- [x] API/design/evidence and selected-scope progress updated.

## Vector inverse checkpoint

The selected-inverse increment passes 31 strict source statements, 43 imported statements and three refusal controls, all on the pinned binary. The wider A–B and FTA target remains active; finite-family sums are next. See check.py and check.py.

## Later checkpoints and current dependency

Finite-family sums/directness and pair criteria have accepted receipts. The
scalar-space/1B concordance checkpoint accepts 34 vector_space statements and
32 imported statements. Initial polynomial functions pass 36/31 statements;
the same-bound evaluation laws then pass 40/26, each with three refusal
controls. No polynomial-space closure, degree or FTA completion is claimed.
The current dependency is first-class evaluation and transport of existing
linear combinations to polynomial values. The 1.8 reverse-domain gap remains
pending a separate scope choice; its source-owned reproduction/todo are in
list_domains.
