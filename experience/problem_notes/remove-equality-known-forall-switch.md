# Replacing the equality/known-forall switch with proof-search rounds

## Task context

- Task: remove `VerifyState::equality_may_use_known_forall` and use the existing round boundary.
- Scope: verifier proof-search state, equality and well-definedness callers, cart projection forall requirements, and focused regressions.
- Related workspace: golitex verifier.

## Original blocker

`VerifyState` carried an equality-specific boolean solely to prevent selected
subchecks from reopening known-forall equality search. The cart projection
helper made the coupling especially visible:

```rust
VerifyState::after_well_definedness().without_known_forall_for_equality()
```

The boolean duplicated the structural meaning already represented by
`proof_search_round` and left redundant disabling calls in final-round paths.

## Solution

The cart helper now enters round 1 explicitly:

```rust
VerifyState::after_well_definedness().with_next_round()
```

Round 0 remains the ordinary search root and is the only round allowed to open
known-forall equality search. Already-final membership requirement checks keep
their final-round state without an extra switch. Well-definedness entry points
preserve the caller's state, so they do not unnecessarily disable legitimate
non-equality known-forall verification. The field, transition method, and all
call sites were removed.

A negative regression stores a forall whose equality conclusion requires
itself. The concrete goal returns `UnknownError` instead of recursively
re-entering the same forall. Existing positive regressions retain ordinary
known-forall equality and cart extensionality.

## Verification

- `cargo build --release`: passed.
- `cargo fmt -- --check`: passed.
- `cargo test --release verify_state_ -- --nocapture`: 2 state tests passed;
  the matching source-architecture test also passed.
- `cargo test --release circular_known_forall_equality_requirement_stops_after_one_round -- --nocapture`: passed.
- `cargo test --release have_cart_can_equal_literal_cart_by_dimension_and_projections -- --nocapture`: passed.
- `cargo test --release known_forall_equality_uses_indexed_function_head -- --nocapture`: passed.
- `cargo test --release --lib`: 1150 passed, 4 failed, 8 ignored. The four
  remaining failures are outside this state change: three stale output
  assertions still require `"atomic fact unknown"` while current output is
  `UnknownError` with `unknown_result.type = "unknown"`; the fourth is the
  concurrently edited odd-sum To-Lean golden comparison.

## Reusable lesson

When a proof-search permission is exactly equivalent to being at the ordinary
root, represent it through the existing round transition. A dedicated boolean
is unnecessary unless callers need a real combination of permissions that no
existing structural phase can express. Keep special builtin helpers from
creating a fresh round-0 full-search root after they have already selected a
forall candidate.
