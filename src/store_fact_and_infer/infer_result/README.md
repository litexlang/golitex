# Inference results by source family

`InferResult` mirrors all ten `Fact` constructors. `InferAtomicFactResult`
mirrors all 42 `AtomicFact` constructors directly. Each atomic constructor
contains `Vec<Infer{Family}Result>`: all applicable direct rules run in the
existing order, rather than selecting one winning proof route.

For example, the actual prime branch is:

```rust
pub enum InferPrimeFactResult {
    Definition(InferPrimeDefinitionResult),
}

pub struct InferPrimeDefinitionResult {
    pub source_fact_id: FactId,
    pub lower_bound: StoreInferredFactResult,
    pub trial_divisors: StoreInferredFactResult,
}
```

The enum identifies the rule. Its leaf captures the executed instance and the
two actual stores. No string rule registry or parallel inference tree selects
its meaning. Families with no rules have empty rule enums and return an empty
vector; `Some(empty-family-result)` means inference ran, while the seed's
`infer: None` means inference was disabled.

`InferSubsetFactResult` can retain both `FiniteUpperBound` and
`ElementwiseMembership`, in that execution order. Equality retains each
matching cancellation or power transport independently. Existing And/Chain
seed components run their direct atomic rules; derived compounds only index
their components.

Fixed outputs have semantic field names: prime's lower bound/trial divisors,
coprime's not-both-zero/gcd-one, interval membership/bounds, and function image
membership/witness. Variable outputs retain their owning sequence. Cartesian
coordinates record the zero-based original factor index. Builder projections
select `BaseMembership` or `Condition { condition_index, stored }`, where the
index belongs to the selected builder's original conditions. Duplicate stores
can be omitted without renumbering the remaining source conditions.

Actual condition evidence stays on the rule leaf. Cancellation retains its
membership/nonzero proofs. Positive-power transport retains the checked power
or base positivity route and the real-exponent proof, alongside its source
FactId, selected power and direct store. Capturing those existing proofs adds
no new checks or proof search.

Each conclusion is `StoreInferredFactResult { store }`. The named rule owns
formation and truth from its checked source and genuine applicability
conditions. Direct storage never calls conclusion WD or inference. Premise
checks run with inference disabled. An explicit later statement may check a
stored conclusion and use it as a new seed. See the
[one-step contract](../one_step_acceptance.md).

`stored_conclusions()` and `stored_fact_ids()` are computed views over the
actual captured stores, preserving their execution order and original IDs.
They do not allocate proof IDs, own new stores or authorize compiler support.
JSON retains its existing public projections. Lean dispatches supported named
rules into proved `Litex.lean` adapters and uses the original source cursor.
Unused unsupported inference retains the existing boundary; consuming its
conclusion rejects because no reviewed Lean producer exists. Prime inference
and positive-power transport do not gain Lean adapters from this type change.
The complete compiler run still needs its read-only Runtime for exact citation
payloads; an isolated inference result is not a standalone citation closure.

The strict [family tracer](../../../examples/infer/atomic/infer_result_rule_families.lit)
checks prime/coprime/proper-subset, simultaneous subset rules, Cartesian factors
and builder projections. The
[one-step tracer](../../../examples/infer/atomic/one_step_store_only.lit) checks
FnRange cycles, growing builders and explicit next seeds. Rust controls also
check actual IDs, no-rule versus disabled results, real premise evidence,
missing or corrupted builder condition indices, unsupported consumed rules,
pending stages, closed scopes and rollback.

Acceptance uses `cargo test --release --all-targets`, strict release execution
of all infer examples, the README/docs fence runner, and actual regeneration
plus pinned Lean checking of the affected compiler pairs. The final checkpoint
below records the completed gate scope and counts.

## Verified checkpoint, 2026-10-13

- Release build and `cargo test --release --all-targets` exit 0: 1,684 library
  tests and 42 integration tests pass, with no failures or ignored tests.
- All 44 `examples/infer/**/*.lit` files pass strict release CLI execution;
  all 916 executable README/docs fences pass the repository fence runner.
- Complete Normal JSON for `one_step_store_only.lit` and
  `additive_cancellation.lit` equals the captured pre-migration output.
  `$prime(4)` still fails ordinarily with `session_terminated: false`, `termination: null`.
- Thirteen existing pairs pass strict source execution, actual compiler
  generation and Lean 4.31.0 with warnings as errors: additive, subtractive,
  multiplicative, common-denominator and nonzero-numerator cancellation;
  nonnegative-real property; nonnegative-square theorem; closed unit interval;
  subset-real membership/order; mixed real order chain; positive-integer natural
  square; finite natural set; and chain-guard reciprocal. `Litex.lean` passes
  the same real Lean gate. Every saved pair equals a fresh compiler generation.
- Four stale paired outputs were regenerated: closed unit interval,
  subset-real membership/order, positive-integer natural square and chain-guard
  reciprocal. Their old/new text differs only by consistent `h_<FactId>`
  renaming. No generated proof was handwritten.
- Real Lean `#print axioms` checks all 47 public theorems in those pairs. Their
  only observed axioms are `propext`, `Classical.choice` and `Quot.sound`; no
  generated proof holes or project axioms occur. This gate covers these pairs,
  rather than claiming a full compiler corpus or native-model audit.
- The final architecture audit checks exact input/result variant order,
  exhaustive owning dispatchers, removal of the old flat/grouped result types,
  direct storage without WD/infer, inference-disabled premise checks, and no
  changed AST/Runtime/Env owner files. Root `scripts/` stays ignored and
  untracked. Whitespace checks pass.

Snapshots, persistent Session journal, compatibility comparisons and Rust/CLI
receipts remain in the task-owned `tmp/2026-10-12/infer-result-enums/` area.
Compiler generations, pinned toolchain metadata, Lean builds, drift checks and
axiom receipts remain in the ignored local workspace
`scripts/litex_to_lean/.draft/infer-result-enums-2026-10-12/`.
