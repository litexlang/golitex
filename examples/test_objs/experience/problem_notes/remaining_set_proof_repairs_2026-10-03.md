# Explicit set proof repairs — 2026-10-03

17 of the remaining 22 goals are restored by checked Litex authoring. No Rust, framework, AST, state or trust changes.

## Tracer

Before: `family_union({{1}, {2}}) = {1, 2}` fails WD on distinctness.
After: prove `{1} != {2}` by contra using witness 1, eliminate union membership with obtain/cases, prove both member directions, then `by extension`. P04 consumes the same proved equality and `1 $in {1, 2}`.

## Closed cases

family_union-P03, family_union-P04, family_union-P05, family_intersect-P04, power_set-P06, index_union-P02, range-P04, range-P06, closed_range-P04, finite_seq_set-P05, seq_set-P03, seq_set-P04, finite_set_size-P05, identifier_with_export_file_id-P04, identifier_with_export_file_id-P05, identifier_with_mod_and_export_file_id-P04, identifier_with_mod_and_export_file_id-P05.

- range/closed_range: expand known membership, explicit cases, finite enumeration for reverse direction, extension. Excluded range endpoint uses contra.
- powerset: explicitly chain empty and singleton powerset equalities.
- indexed union: k=1, k in N, every singleton member in N, subset, powerset carrier, then declaration and fiber equality.
- sequences: pointwise return membership followed by existing fn_set_member. No new extension syntax.
- imports: release obj def at each actual qualified owner, then tuple dimension. Separate file/module contexts retained.
- Adjacent preexisting failures: range(2,2), range(3,1), closed_range(3,1) receive checked contra/extension proofs. Negative index_union N03 receives valid return-carrier proof before wrong index domain rejection.

## Verification and limits

Stable current-source release: 11 complete owning files, 65 positive cases, 28 adjacent negative files; exit, success, statement results and session_error checked. Five unchanged gap fixtures still reject. AST/manifest audit: 99 leaves/files; inventory 644 positives, 295 negatives, 5 gaps. This is a focused acceptance, not a claim that unrelated whole-corpus failures disappeared.

Remaining family_intersect P01/P02/P03 lack usable member directions. index_intersect P02 has a verified return carrier and enumerated all-fiber premise, but direct intersection-member introduction fails. cart P04 has shape and coordinate facts, but the quantified coordinate requirement remains unproved. Details and alternate attempts live in the active plan and journal; no conjectured repair is marked solved.

[Proof journal](../../proof_journals/remaining_set_proof_repairs_2026-10-03.json) contains exact code, outcomes, original retired fixtures and immutable source/binary hashes. Persistent sessions use current strict CLI/sketch, because the older skill flags are unsupported. Ordinary session stdout reports only success/error; clean JSON file gates provide independent confirmation.
