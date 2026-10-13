# Forward-inference search audit

Verified on 2026-10-11, after the positive-power repair. This audit found no
second confirmed instance of an optional truth premise using the caller's
full strategy/definition search permission. It made no additional Rust behavior
change. The README's stale description of the power fallback was corrected.


This is a historical audit of the WD-before-storage implementation. The
current [one-step contract](one_step_acceptance.md) stores internally generated
conclusions under their named rule without rechecking derived WD; its genuine
applicability premises still use bounded verification with inference disabled.

## Central before/after invariant

Before the preceding repair, the fallback inside `positive_real_power.rs` used:

```rust
self.verify_atomic_fact(&base_positive, verify_state)?
self.verify_atomic_fact(&exponent_in_r, verify_state)?
```

The accepted implementation derives one restricted child for all three
optional premises:

```rust
let premise_state = verify_state.capped_at(VerifyStateLevel::BuiltinRule);
self.verify_atomic_fact(&power_positive, premise_state)?
self.verify_atomic_fact(&base_positive, premise_state)?
self.verify_atomic_fact(&exponent_in_r, premise_state)?
```

An unavailable optional premise skips this rule. The seed's truth and formation
remain checked; derived-fact WD still uses the original caller state. The
maintained tracer is [positive_real_power_bounded_premises.lit](../../../examples/infer/equal/positive_real_power_bounded_premises.lit).
Its unchanged square-equality statement is accepted:

```litex
forall x, y R:
    x^2 = y^2
    =>:
        x^2 >= 0
```

## Call inventory and classification

The current `src/store_fact_and_infer/` tree contains 46 Rust files and 12
direct `verify_*` / `search_*` calls. All were classified, including the
cancellation helpers' callers:

| Calls | Owner | Classification |
|---:|---|---|
| 3 | Positive-real power | Optional positivity/type premises, capped at BuiltinRule |
| 4 | Strict/weak lower bounds | Optional sign/integer premises, capped at KnownSpecialProperty |
| 1 | Subset finite upper bound | Optional upper finiteness, capped at KnownSpecialProperty |
| 2 | Cancellation helpers | Optional scalar/nonzero premises; every addition, subtraction, product and quotient caller supplies a KnownSpecialProperty cap |
| 1 | Template builder projection | Required instance WD before substituting the selected template RHS |
| 1 | Preimage projection | Required complete-domain and generated-builder construction evidence |

No forward-inference owner creates a fresh `VerifyState::top_level()` or
`VerifyState::new(...)`. The audit also followed exact-property lookup,
function-domain construction, template RHS substitution, closed-number
resolution, builtin definition builders and the inferred-store helpers.
Structural lookup and substitution do not perform independent theorem search.
Construction and derived stores retain their inherited formation checks:

```rust
let well_defined = self.verify_fact_well_definedness(fact, verify_state)?;
// Only a successful formation check proceeds to store/infer.
let store_and_infer = self.store_fact_and_infer(fact, verify_state)?;
```

The two construction calls are not analogous optional truth fallbacks. Reducing
their permissions or omitting their evidence would change the existing
formation contract.

## Recursive consequence boundaries

Existing guards were inspected and exercised: cancellation skips known
equality endpoints; natural-membership/sign propagation skips a known natural
membership; builder projection skips exact stored consequences while visiting
new carrier conditions; preimage projection avoids re-entering an active
construction. Tests retain late-certificate, late-carrier, nested-inference,
negative-domain and failed-statement rollback behavior.

Chain closure enumerates pairs in the finite input chain and retains each
premise-edge path. Long chains can therefore generate substantial output. This
is a size-dependent cost in the existing result contract, not an observed
unbounded optional search or a newly confirmed defect.

## Executed acceptance

```bash
cargo test --release --lib -- store_fact_and_infer:: function_preimages native_scalar_codomain finite_set_cardinality_rule chain_fact mixed_equality_order_chain --nocapture
```

Result: **79 passed, 0 failed**, process exit 0. This includes optional-premise
permission tests, stored consequence/provenance tests, cycle/replay tests,
required template/preimage guards and negative/rollback cases.

Every `.lit` under `examples/infer/` was independently run with:

```bash
target/release/litex -strict -lang en -f <example>
```

Result: **42/42 files, 166 top-level statement results**; each process exited
0 with a Normal `kind: run`, `run_result: "success"`, `session_terminated: false`, `termination: null` envelope.
No new trust or assumption was added.

CLI binary SHA256:
`6dd96443ae283a98f9958e54fe54a940d41aaa6a465d71b2485d7d0522a2ff26`.
Raw envelopes, source hashes, call inventory and test output are retained in
the ignored task draft `tmp/2026-10-11/infer-search-audit/acceptance.json` and
its sibling artifacts.

These results certify this call audit and these executed cases. A search-stage
ceiling is not a wall-clock or recursion-depth bound. This audit does not claim
that every possible inference input, required WD check or explicit strategy
search has a universal time bound.
