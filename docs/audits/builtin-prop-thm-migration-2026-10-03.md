# Builtin prop / theorem migration, 2026-10-03

Task: make closed complex inequalities calculable, audit and restore legacy builtin predicates/theorems, and explain the template/struct field failures. Scope: the current `src/` implementation and `scripts/memorial_legacy_src/`, strict release examples and focused Rust evidence. This is a bounded migration audit, not a complete system scan.

Machine evidence: [literal sources, session and gates](../../examples/proof_nodes/proof_journals/builtin-prop-thm-migration-2026-10-03.json). Drafts and raw compilation logs remain in `tmp/2026-10-03/builtin-prop-thm-migration/`. No trust was inserted and no AST/Env/Runtime shape or search permission was changed.

## Verified user-visible paths

```litex
i != 0
release thm real_least_upper_bound_exists({0}, 1)
obtain upper from exist L R st {$is_real_least_upper_bound({0}, L)}
release thm real_member_le_least_upper_bound({0}, upper, 0)
0 <= upper
```

The direct inequality reports `by_closed_calculation` in ten fresh processes. The bounds producer and its consumer now pass. A fresh bare certificate, `by def` on the opaque certificate, empty/unbounded premise cases and bad arity still reject.

- Calculation was already wired in the current release; this task verified it and preserved a [direct calculation tracer](../../examples/proof_nodes/atomic/direct_closed_complex_calculation.lit). This does not establish that every explicit contradiction or strategy recursion path is fixed.
- The bounds theorem entry already existed. Its generated normal atomic predicate lacked builtin WD recognition. The two reserved, plain certificate names now have arity-two signatures, with ordinary argument WD; a signature never grants truth. Qualified user predicates keep their normal owner lookup.
- `by def $surjective(...)` already had a definition handler. The original finite example needed an explicit checked universal preimage proof. Positive injective and surjective facts also lacked legacy's publication of their quantified defining clauses; that publication is now restored with source and derived FactIds.
- Choice definition verification existed. Equivalent callable carriers were accepted for ordinary mapping properties but not for choice. Both independent callable obligations now retain their actual declared signatures and checked carrier equalities. The structural identities `family_union({A}) = A` and `family_union(power_set(A)) = A` supply the required equalities. Each has its own proof variant and bilingual Normal / Detailed output.
- Restored mapping inference initially exposed a finite-sequence WD failure: the generated universal used `closed_range(1,n)`, while the callable signature used `N+` with `k <= n`. Integer intervals with a positive integer literal lower bound now publish their `N+` carrier alongside bounds. No recursive permission was reopened. Lower bounds zero/negative and mismatched prefixes remain rejected.

## Exact surjective and choice proofs

```litex
have fn identity(x R) R = x
claim:
    ? forall y R:
        exist x R st {y = identity(x)}
    witness exist x R st {y = identity(x)} from y
by def $surjective(R, R, identity)
```

[Surjective definition tracer](../../examples/proof_nodes/atomic/by_definition/builtin_surjective.lit). A constant function on `R -> R` still cannot prove surjectivity or injectivity by definition without valid defining clauses. Publication consumers have separate [injective](../../examples/infer/atomic/injective_definition.lit) and [surjective](../../examples/infer/atomic/surjective_definition.lit) tracers.

```litex
have fn family(alpha {1}) power_set({1}) = {1}
have fn choice(alpha {1}) {1} = 1
forall alpha {1}:
    choice(alpha) $in family(alpha)
by def $is_choice_function_for({1}, power_set({1}), family, choice)
```

[Choice definition tracer](../../examples/proof_nodes/atomic/by_definition/builtin_choice_function.lit). Wrong family or choice codomains still reject. This repairs the callable/definition composition; it does not introduce arbitrary callable variance.

The original [finite surjection cardinality example](../../examples/proof_nodes/atomic/by_builtin_rule/less_equal_finite_set_size_surjection_codomain_le_domain.lit) now includes checked `1 $in A`, a universal with explicit singleton membership and preimage witness, and explicit numeric carriers for both finite sizes. It preserves the same `finite_set_size(B) <= finite_set_size(A)` goal. The prior source is retained as comments.

## Legacy inventory

The historical predicate recognizer contains 27 names. Current treatment:

| Names | Current contract / migration evidence |
| --- | --- |
| `=`, `!=`, `<`, `>`, `<=`, `>=` | Dedicated atomic variants; closed calculations and existing rules. False complex comparison/order controls are in this journal. |
| `is_set`, `is_nonempty_set`, `is_finite_set`, `is_cart`, `is_tuple` | Dedicated variants and intrinsic/known/builtin routes. This inventory does not certify every symbolic composition. |
| `subset`, `superset`, `proper_subset`, `proper_superset`, `in` | Dedicated variants; definition and elementwise publication paths exist. Symbolic chained finiteness remains a residual below. |
| `injective`, `surjective`, `bijective` | Definition builders exist; positive injective/surjective publication restored. Bijective publishes its two component properties and now their quantified bodies. |
| `prime`, `coprime`, `dvd` | Existing definition, builtin and inference paths retained. No extra number-theory capability claim from this name audit. |
| `is_choice_function_for` | Existing definition/pointwise publication plus repaired equal-carrier WD composition. |
| `is_real_least_upper_bound`, `is_real_greatest_lower_bound` | Reserved opaque arity-two certificate signatures restored; producer/consumer and no-fabrication gates. |
| `fn_eq`, `fn_eq_in` | Deliberately removed in the current Manual; ordinary equality / `by fn_extension` replace them. They were not reintroduced. |

All **25** legacy theorem names are already present in the native current catalogue. No missing legacy theorem name was found. The final shared workspace also contains three additional intersection theorem names, for 28 current entries. All 28 strict [native theorem tracers](../../examples/stmt_nodes/release_and_expand/builtin_thm/) pass the captured release CLI gate, including both completeness theorems and finite bijective enumeration. The journal retains the exact names, source and results. A present theorem name is not evidence that every automatic predicate search path has migrated.

## Struct: three separate observations

Follow-up on 2026-10-04: the template/alias callable and tuple-value composition below is now repaired; the unchanged Triple prefix and direct field queries without an intermediate tuple assertion pass. See the [verified solution record](../../examples/proof_nodes/experience/problem_notes/template-alias-struct-tuple-2026-10-04.md). The failures described below retain the original 2026-10-03 checkpoint; one-field structs remain unsupported.

```litex
struct Triple<X set>:
    first X
    second X
    third X
have chosen_struct &Triple<R> = (1, 2, 3)
chosen_struct.first = 1
```

This direct typed construction and field equality **pass**. General field projection is supported.

The original [template alias example](../../examples/stmt_nodes/definition/let_template_struct_aliases.lit) contains:

```litex
let triple_R = \triple<R>
let chosen = \triple<R>(1, 2, 3)
triple_R(4, 5, 6) = (4, 5, 6)
chosen = (1, 2, 3)
have chosen_struct &Triple<R> = chosen
chosen_struct.first = 1
```

In a separately run prefix that excludes the later single-field declarations, the first function application fails WD with `no matching function signature`; `chosen = (1,2,3)` and the final field equality also fail. The typed `have` itself succeeds. It supplies a direct struct view and structural projection bridges, but the earlier template/alias value chain still does not establish the specific tuple coordinates. Classification: wiring/composition and representation evidence, earliest observed owner callable WD; the exact migration/implementation root cause remains open. Next investigation: trace template specialization's FnSet registration and alias/value equality through the existing callable owner before changing field representation.

```litex
struct ScalarOps:
    add fn(x, y R) R
```

This fails during parsing: `struct definition expects at least two fields`. The following `Space` also has only one field. `release_one_struct_layer.rs` independently enforces the two-field tuple/cart contract, so deleting only the parser guard is insufficient. Classification: current syntax/representation limit, independent of the earlier field proof. Supporting a one-field struct requires an explicit representation decision; no such change was made.

## Verification and residuals

The final captured strict CLI matrix has 72/72 expected outcomes: 28 theorem tracers, 12 affected artifacts, ten fresh calculation checks, 19 false/domain/missing-premise controls and three struct boundary checks. Expected struct rejection is recorded as a boundary, not called fixed.

The initial focused Rust gates selected 52 core tests covering mapping publication, certificate signatures, predicate domains, native theorems, function WD evidence and JSON acceptance. They passed at the recorded checkpoint. An initially misspelled cardinality filter selected zero tests and was corrected; the actual additional seven-test gate had three passes and four failures. Those results belong to their exact compiled checkpoint, not automatically to later workspace source.

The extra symbolic finite-set cases are distinct from the restored concrete surjection example:

```litex
forall A, B set, F finite_set:
    A $subset B
    B $subset F
    =>:
        $is_finite_set(A)
```

This remains rejected in the captured release probe. A direct finite upper set succeeds. The four Rust failures also cover combined subset/cardinality proof and explanation cases; one combined CLI case later passed on a newer release binary. Source/binary snapshots changed between checkpoints; entry/context differences also need investigation. This task does not assert an unverified common cause or attribute those failures to its local repairs. Keep the chained finiteness and exact Rust gate open pending a stable rebuild and owner diagnosis.

The workspace was changing during final verification. A later source snapshot introduced `ByStructuralMembership` and temporarily failed release compilation at its private import and missing output arms. The machine journal records build status and identities; the successfully run CLI binary must not be mistaken for that failed source snapshot. Final build/gate status is updated separately below.


## Final stable checkpoint

Release build succeeded with source SHA-256 `7e33848432a75d992b3876dc3776ac01f271fb6ddc952c1a2709ad7f44e0014e`
and binary SHA-256 `b0360930197e6bc039b3863a67c467a3f64590b3ab7a71d545f15e74bf7014b8`.
The source was stable through that build and verification window. Other workspace changes occurred after those gates, so the later source snapshot is not covered by this checkpoint.
All 72 strict CLI outcomes matched expectations, including all 28 current
native theorem tracers (25 historical names plus three current additions).
The focused Rust suites ran 61 tests: 57 passed and four finite-cardinality
cases failed. The 54 core mapping/theorem/WD/JSON/function tests all passed;
the extra cardinality suite had three passes and four failures. No zero-test
filter is counted. The cart-dimension fixture was updated for the current
legal intrinsic-codomain route, retaining its invalid-shape rejections.

The final exact template prefix still rejects the callable application and
field-value chain; the direct typed tuple/field case passes. Single-field
struct parsing still rejects. These and chained symbolic finiteness remain in
[the source-owned residual list](../../examples/proof_nodes/TODO.md).
This completes the bounded local repairs and audit; it does not close those
remaining problems or claim a whole-system/Lean gate.
