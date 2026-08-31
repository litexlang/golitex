# Runtime Failures Correlated to Result/Compiler Boundaries

Recorded from the H3 integration family audit and the first H4 all-example
matrix. This file narrows repair sites; it does not authorize edits in active
user-owned compiler paths.

| Failure | Phase | Exact compiler boundary | Result evidence already observed | Smallest next gate |
| --- | --- | --- | --- | --- |
| Example 12 / named real function | Rust fail-closed | `proof_rendering/function_reduction.rs:390` rejects the target argument `((a : ℝ) : ℂ)` as unrelated | checked function-reduction Result and real-domain membership exist | retain or derive the exact selected-carrier equality, then kernel-check Example 12 |
| Example 23 / multilayer domain | Rust fail-closed | `fact_compilation/universal_facts.rs:645` installs conclusion WD stores; the requirement then rejects native-real `a` against `Positive a` or selected-carrier `Lt` | parameter-index and ordered domain Results are present | normalize one requirement representation at WD installation, with mismatched layer/order negative tests |
| Example 24 / anonymous function | Rust fail-closed | `source_rendering/function_values.rs:256` sees no active Result-owned WD context | captured JSON contains `AnonymousFunctionBodyMembership`, `AnonymousFunction`, and `FunctionHead` | activate the parent WD context around object-reflexivity rendering; do not reconstruct it from syntax |
| Example 26 / integer-range sum | Rust fail-closed | `source_rendering/aggregate_objects.rs:19` sees no active Result-owned WD context | captured JSON contains finite-set/list evidence and the inventory finds the aggregate WD Result family | activate the exact iteration owner context and require its Z-to-Z contract before rendering |
| Example 57 / known-forall projection | Rust fail-closed | `proof_rendering/exact_predicate_transport.rs:299` rejects parameter 0 changing from `(2 : ℝ)` to `(2 : ℂ)` | exact source FactId and both projected conclusions are retained | choose the user-approved exact-carrier transport, then prove both projections reuse the same source FactId |
| Nested-forall probe | Generated Lean reject | generated line 9 gives `fnApply` a proof of `In __p1 R` where function membership is required | compiler returns a complete source module, so Rust-only tests miss this | fix binder alias selection and require the focused generated module to pass real Lean |
| Example 10 / theorem-instantiated existential | Generated Lean reject | `theorem_compilation/theorem_instantiation.rs:429` emits `self_exists (3 : ℂ)` after `self_exists` changed to require `Litex.R.Carrier` | existential Result and projected conclusion exist | instantiate with the selected exact carrier representative and replay its membership proof |
| Example 14 / set-builder choice | Generated Lean reject | `proof_rendering/set_builder_membership.rs:45` emits a direct subtype witness whose equality proof has the wrong simplified type | base membership and predicate proof are retained | use the reviewed `inSetBuilder` adapter or prove the exact subtype transport, then kernel-check Example 14 |
| Example 8 / proof scope | Generated Lean reject | generated line 25 passes a value with the wrong exact-carrier type | proof-scope Result compilation succeeds in Rust | isolate claim/example carrier transport and kernel-check Example 8 |
| Example 36 / known-forall composition | Generated Lean reject | generated line 15 fails after simplification | known-forall Result composition succeeds in Rust | align the projected conclusion carrier before publishing its FactId |
| Example 62 / builtin theorem application | Generated Lean reject | generated line 18 supplies an argument of the wrong type to the selected theorem | theorem identity and application Result are retained | validate exact argument carriers before emitting the registered theorem call |
| Example 68 / transparent set membership | Generated Lean reject | generated line 26 fails after simplification | transparent definition and membership Results are retained | preserve the set-carrier transport through transparent unfolding |
| Example 69 / real Cauchy | Generated and checked Lean reject | generated line 127 has a simplification type mismatch; checked line 122 hits forbidden large elimination from `Prop` | completeness Result tree compiles in Rust | redesign the elimination route without large elimination and kernel-check both copies |

## Dependency order

1. Freeze `UD-2` numeric/exact-carrier observation; it affects Examples 10,
   12, 23, and 57.
2. Repair WD context lifetime for Examples 24 and 26 without changing their
   carriers.
3. Repair nested binder alias selection.
4. Repair set-builder subtype transport.
5. Only then synchronize generated assertions/files; otherwise regeneration
   would bless invalid Lean or hide fail-closed compiler gaps.

## H3 six-gap ownership audit

The six red integration rows are not six new semantic questions:

| Gap | Semantic dependency | Edit dependency | Ready before decision? |
| --- | --- | --- | --- |
| named real function carrier | `UD-2` exact-carrier observation/transport | `UD-1` handoff of function reduction | no |
| multilayer application carrier | `UD-2` exact-carrier observation/transport | `UD-1` handoff of universal-fact WD install | no |
| known-forall multi-conclusion carrier | `UD-2` exact-carrier observation/transport | `UD-1` handoff of exact predicate transport | no |
| anonymous function WD context | existing Result-owned-scope contract | `UD-1` handoff of function-value rendering | yes after handoff |
| aggregate WD context | existing Result-owned-scope contract | `UD-1` handoff of aggregate rendering | yes after handoff |
| nested-forall binder alias | existing FactId/binder-identity contract | `UD-1` handoff of the focused replay slice | yes after handoff |

Therefore Codex can take the latter three as bounded mechanical slices once
the active-file boundary is handed off. The first three must remain
fail-closed until `UD-2`; choosing a coercion inside a renderer would silently
set the numeric ABI.
