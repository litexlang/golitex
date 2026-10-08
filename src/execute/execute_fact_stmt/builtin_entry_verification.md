## Structural membership increment (2026-10-03)

Direct now has a separate `ByStructuralMembership` success route, after known
proofs and pure closed calculation. Constructor descent uses no verifier/search
callbacks; raw known leaves and fixed checked builtin codomains supply types.
The shared search level table and WD-before-search contract remain in force.
The entry is `search_atomic_fact_proof_directly`; no compatibility alias is kept.
New tracers: `examples/proof_nodes/atomic/direct_structural_membership.lit` and
`examples/proof_nodes/equal/by_known_special_property/fn_tuple_carrier_after_equality.lit`.
Seven new Rust regression tests pass, covering carrier composition, citations,
JSON, WD rejection, no SP escalation and no fact publication. The two maintained
CLI tracers, both vec controls, actual Manual code, nine survey positives and
three negative boundaries pass. Final fixed checkpoint: 710 library tests pass,
27 fail; statement integration still fails. Baseline: 685 pass / 34 fail plus
that integration failure; no new failing names. Concurrent changes prevent
attributing every global recovery to this increment. Source was stable during
the checks; later worktree edits are outside that fixed evidence.

After batching repeated carrier scans, the long release/read probe passes in
about39.9s; whole geo still times out at45s. A frozen on/off comparison of the
reduced similarity definition runs in about13.4s/12.7s, versus22.7s enabled
before batching. This is a single-run diagnostic, not a stable benchmark. The current
persistent-prefix diagnostic reaches a slow `are_triangles_similar` definition;
this is recorded separately from the repaired squared-difference WD example.
Acceptance details are recorded in the geo migration journal. Earlier counts
below are historical checkpoints, not this increment's final gate.

# Direct level 0 — 2026-10-03

Status: Direct increment complete; broader geo migration remains incomplete. Final comparison is recorded in
`plan/迁移的plan/proof_journals/verify-state-level-implementation.json`.

`VerifyState` retains exactly `level` and `can_rewrite`. Level 0 is now Direct:
identity/pairwise structural alpha and exact stored path/citation evidence first, closed exact calculation
second. `DirectAtomicFactSearchResult` explicitly distinguishes `ByKnownFact`,
`ByClosedCalculation` and `NotFound`. Calculation evidence mirrors the atomic
family and records equality values, comparison polarity, or membership value/set.

On 2026-10-06 the user approved removing graph-wide alpha endpoint/path
discovery from ordinary lookup and forall aliases. Pairwise nested alpha and
existing Strategy-level local peer comparison remain. That change is implemented
but untested at the user's request; see the equality README and local-alpha-only
acceptance note. Historical validation below predates that change.

The calculator is a free function without Runtime/State/search callbacks. It
uses classified decimal arithmetic and exact rational/complex evaluation.
Unknown/false/undefined/overflowing expressions produce no proof. Existing raw
known readers stay calculation-free. Symbolic normalization and tuple/finite-set
shape calculations retain their higher routes; complete verify still checks WD.
No AST, owned Runtime/Env state, trust, axiom or geo proposition was changed.

The maintained [Direct tracer](../../../examples/proof_nodes/equal/direct_closed_calculation.lit)
restores this unchanged source without preliminary numeric memberships:

```litex
by enumerate finite_set:
    ? forall x {1,2}:
        x > 0
```

`1/3 < 1/2` is available at Direct; `1/0=1/0` still fails WD. SP can now close
`(1+3,2+4)=(4,6)` by constructor descent and Direct leaves. Likewise an existing
list builtin may win before its strategy now that numeric WD/premises are
available. Tests check the new winning route and retain explicit strategy
certificate coverage rather than disabling the original mathematics.

Validation: 13 permission tests, 29 equality-search tests, 6 list-membership
contract tests and 7 normal-JSON tests passed in the full release checkpoint.
Global compatibility remains a separate open item; see the current journal for
full counts, concurrent-source caveats and surviving geo failures.

Documentation impact: Manual/FAQ and this architecture README specify Direct;
the new `.lit` is the executable migration; normal/detailed JSON and typed result
tests distinguish calculation from citation. Old builtin calculation evidence
remains for direct builtin callers and symbolic higher-level routes. A missing
`JsonValue::Array` constructor in a concurrently edited projection was also
repaired as a local compile fix; it does not change the Direct policy.

Current release build and direct CLI positive/negative gates pass. Last completed
worktree full gate: 637 passed / 52 failed, with statement integration failing.
The latest test compilation was blocked by an unrelated in-progress registration
of missing `tests/unit/execute/struct_dependent_fields/tests.rs`. A frozen candidate
whose Direct source hashes match the current worktree independently passes all
69 focused tests listed above (including 14 additional JSON acceptance tests).
Its full run has three extra import-alias fixture-path failures from relocation;
that snapshot count is not a new production regression claim.

A paired fixed-source build changes only whether the Direct calculation branch
runs: finite enumeration fails without it and passes with it; both versions fail
the long geo prefix at `(b[1]-a[1])^2 $in R`. Full geo still times out at 45s.

---

## Historical pre-Direct checkpoint (superseded by the Direct receipt above)

# Shared search-level migration — 2026-10-03

Status: implemented core, compatibility gate still failing. This supersedes the
boolean/depth policy in the historical receipt below.

`VerifyState` has only `level` and `can_rewrite`. One atomic search schedule
serves both families. Stages and their premise ceilings are 0: no new search;
1/SP: 0; 2/builtin: 1; 3/strategy and 4/definition-forall: 2. Rewrite is admitted
at (4,true) and continues at (4,false). Pure constructor traversal has a fixed
leaf ceiling; a searched peer bridge cannot reenter the peer stage.

WD and infer receive the caller ceiling. Exploratory WD returns evidence;
the existing checked-fact commit records direct atomic subjects in its current
scope. Named identifiers and quantified internals are excluded. Reusing a
stored atomic fact's predicate domain now retains an explicit FactId citation.
No AST or owned Runtime/ExecEnv field was added, and no trust/axiom was added.

Acceptance source: [shared_search_levels.lit](../../../examples/proof_nodes/equal/shared_search_levels.lit).
Permission regressions cover cross-family stage admission, finite congruence,
WD rejection, no speculative cache write, stored-domain citations and rewrite
consumption. The focused permission gate passed 8 tests; the equality-search
gate passed 29 tests. These are not an all-tests-green claim.

## Open compatibility decision

This strict five-level policy removes fresh calculation from builtin premises.
A concrete reproduction is:

```litex
by enumerate finite_set:
    ? forall x {1,2}:
        x > 0
```

Current release rejects it. Prefixing the same source with `1 $in R` and
`2 $in R` succeeds. The symbolic carrier WD needs a finite-carrier membership
rule whose numeric membership leaves cannot enter builtin again at level 1.
The exact source and JSON outputs are retained in the migration journal.

A separate **ClosedCalculation** stage, containing only finite closed numeric
checks with no verify/search calls, is proposed for maintainer choice. It is
not implemented or silently folded into KnownFact/SP. Retaining the strict
five-level table instead requires explicit intermediate premises and further
classification of composed rules. Neither choice alone establishes that all
remaining aggregate, definition and geo cases are repaired.

The source-owned record is [the migration journal](../../../plan/迁移的plan/proof_journals/verify-state-level-implementation.json).
Raw build/test output is in `tmp/2026-10-03/geo-search-level-design/level-migration/`.
The frozen start baseline had 644 library passes, 7 failures, and a passing
50-fixture statement integration gate. Concurrent numerical/parser work means
a raw difference from that baseline is not exclusively attributable to this task.

## Current checkpoint results

- `cargo build --release`: pass.
- `cargo test --release --all-targets --no-fail-fast`: **609 pass / 53 fail** in the library; statement integration fails.
- Permission tests: 8 pass. Equality-search tests: 29 pass. `git diff --check`: pass.
- New shared-level tracer and maintained tuple/function projection tracers: exit 0, success:true, session_error:null.
- Geo without the extra vec equality passes; with that equality it still fails at dot expansion (2.164s).
- The longer theorem release/read probe passes in 17.807s. Full `scripts/geo.lit` still times out at 45s.

These measurements are a checkpoint, not acceptance. The new closed-calculation
policy question is pending; no permission exception has been introduced.

## Historical receipt (2026-10-02, superseded policy)

# Builtin entry verification — 2026-10-02

`VerifyState::can_use_builtin_rule` replaces the builtin round with one boolean
entry permission. `remaining_deep_search_depth` independently starts at 3;
`StrategySearch::DEPTH_LIMIT` remains 16. `after_deep_search` preserves builtin
permission. All constructors and forwarded states carry both fields.

Builtin requirements go through `verify_builtin_rule_premise`. Their truth
search disables ordinary builtin entry, deep search and rewrite. Existing
known/citation and calculation leaves remain available. A stored or literal
function body can supply one checked substitution, with an existing function
path and a checked residual equality; a second body unfold is rejected.
Atomic premise WD keeps caller permissions and equality-peer restrictions,
without storing WD. No mathematical rule, AST field, owned runtime/environment
state, storage transaction, or equality-peer expansion policy was changed.

The runnable acceptance file is
[`builtin_entry_boolean.lit`](../../../examples/proof_nodes/atomic/by_builtin_rule/builtin_entry_boolean.lit).
Its source-order native persistent session and clean strict run both succeed.
The source-owned journal (historical task record; retired)
records the accepted blocks, negative boundaries, CLI compatibility drift and
before/after evidence.

## Visible compatibility boundary

The Manual function-range example formerly proved
`fn_range(shift) $in power_set(Z)` by continuing into subset-definition search
inside the builtin premise. With that route disabled it first states
`fn_range(shift) $subset Z`. The same theorem still verifies separately; the
power-set rule then cites it. The original snippet and its precise changed
outcome are preserved in the journal rather than counted as unchanged source.

## Verification

- `cargo build --release`: pass.
- `cargo test --release --no-fail-fast`: 462 library tests pass; two existing
  tests fail. The statement integration test passes; binary/doc targets have
  no tests. All seven new builtin policy regressions pass.
- The original full pre-edit baseline was 450 pass / one surjection-cardinality
  failure. The additional signature-citation assertion fails intermittently;
  it was reproduced in the pre-edit source reconstructed from Git plus the
  saved initial user diff. Neither issue was changed for this task.
- Same-source comparison of 1,526 eligible examples/docs cases: no new failures
  after the documented Manual adjustment. This includes expected rejections
  and existing known gaps; 1,011 cases succeed and 515 do not. It is a comparison
  gate, not a claim that every repository example is positive or green.
- Active source, tests and maintained docs contain no old builtin-round field,
  constant or decrement helper. `git diff --check` passes.

The two pre-existing failures are
`order_stage_a_finite_set_size_union_and_surjection` and
`bounded_codomain_fallback_retains_its_selected_signature_citation`.
Raw release logs, initial source snapshots and comparison output remain in
`tmp/2026-10-02/builtin-bool-migration/` for review. The disposable reconstructed
checkout and its build cache were removed. Existing concurrent workspace edits
were retained.
