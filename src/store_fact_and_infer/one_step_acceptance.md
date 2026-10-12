# Named-rule, one-step inference

Status: implemented and verified, 2026-10-12. The earlier [termination audit](termination_audit.md) preserves the
pre-change evidence. The former skip-versus-fail question is superseded by the
user's named-rule direct-store contract.

## Contract

A checked seed is stored, then its dispatcher runs once. Each named inference
rule owns the formation and truth of its direct conclusions. Its applicability
conditions remain checked with inference disabled. Storing a conclusion neither
rechecks its WD nor starts another infer pass:

```rust
pub struct StoreInferredFactResult {
    pub store: StoreFactResult,
}
```

The owning `Infer*Result` variant retains the rule identity, original source
FactIds, parameters, genuine premise proofs and exact conclusion stores. JSON
and Lean consume that same typed result. Lean instantiates a proved rule from
`lean/Litex.lean` with the recorded evidence. It does not fabricate a conclusion
WD check or search the completed Runtime for a substitute proof. Missing
adapters reject compilation explicitly; this change does not claim that every
inference family already has a Lean adapter. In particular, prime inference is
accepted in Litex while prime-to-Lean semantic support remains unavailable.

Ordinary input WD, invalid-input rejection, transaction rollback, FactId
indexing, source publication order and closed/future-scope rejection remain.
No Stmt/Obj/Fact AST struct or Env/Runtime owned-state field was changed.

Inferred compounds index their components without inferring them. Original
And/Chain seed components still apply their direct rules. Builder projection
visits the original member once and has no descendant queue. A checked template
or complete preimage signature supplies its definition-owned generated data
without another WD pass. Genuine cancellation nonzero and membership premises
are retained.

## Maintained acceptance examples

```litex
$prime(5)
```

Strict release accepts this source and directly stores `2 <= 5` plus its
trial-divisor universal. `$prime(4)` rejects normally with no derived facts and
`session_error: null`; it is a regression control, not an accepted assumption.

```litex
have f fn(t R) R
forall x R:
    f $in fn(t R) fn_range(f)
    x $in fn_range(f)
    =>:
        x = x
```

Before: this exact input aborted with stack overflow. Now: it terminates and
passes. [one_step_store_only.lit](../../examples/infer/atomic/one_step_store_only.lit)
also covers mutual FnRange cycles, growing builders and explicit next seeds.

```litex
forall a, b, x, y Q:
    (a+x)+y=(b+x)+y
    =>:
        a+x=b+x
        a=b
```

The first infer stores the intermediate equality. Checking that equality as an
explicit statement starts the next rule. Cancellation examples and generated
Lean pairs keep their original premises and final goal. Sequence aliases,
singleton tuple coordinates, preimage singleton values and nested predicate
settings similarly expose their next checked step. No extra mathematical
assumptions were added.

A pure existing subset-membership primitive now answers arbitrary carriers
from two actual stored citations, instead of relying on an inferred universal.
[known_subset_general_carrier.lit](../../examples/wd/known_subset_general_carrier.lit)
checks the element and restricted-function use; missing carrier facts still
reject. Continued export/REPL predicate spellings can cite the same visible
declaration. Other owners with the same printed name do not match; exact-name
candidates retain their existing priority. Module compilation remains outside
the current Lean adapter boundary.

## Verification checkpoint

- All 43 `examples/infer/**/*.lit` files pass current release strict CLI gates.
- All 898 README/docs executable blocks pass the current release fence gate.
- Seven affected pairs pass strict source verification, actual compiler
  regeneration and real Lean 4.31.0 with warnings as errors: additive,
  subtractive, multiplicative, common-denominator, nonzero-numerator
  cancellation, nonnegative-real property and nonnegative-square theorem.
  Current `Litex.lean` also passes. This is a scoped pair gate, not a full
  compiler corpus or native-dependency audit.
- Final `cargo test --release --all-targets` exits 0: 1,680 library tests and
  42 integration tests pass, with no failed or ignored tests. Release build and
  final strict liveness/subset/prime controls also pass. Genuine rule-condition,
  source/citation, permission, future/closed-scope and rollback controls are
  included in this gate.
- The literal-message audit now distinguishes literal `text(` calls from
  helper identifiers ending in `text(`. A concurrent atomic-forall compiler
  fixture keeps an additional identity conclusion so it exercises the intended
  instantiation route instead of whole-forall reuse; its argument-order
  corruption control remains. Concurrent compiler changes were preserved.


Before snapshots, exact CLI receipts, persistent Session journals and Rust/docs
logs remain in the task-owned `tmp/2026-10-12/infer-store-only/` area. Compiler
check receipts/build outputs stay in the ignored local workspace under
`scripts/litex_to_lean/.draft/infer-store-only-2026-10-12/`. Counts are specific
to each gate because independent maintainer changes occurred in this shared
checkout. The completed execution ledger was removed after final verification and
delta/whitespace checks.
