# Strict import cache policy — confirmed defect, decision pending

Task: conversation closeout retest requested 2026-10-04. Scope: non-strict
import-cache replay under strict mode. Label: `kernel_problem`. Category 2
candidate, escalated because cache behavior is a protected shared contract.

The dependency deliberately uses `trust` to declare `0 = 1`; the root releases
that theorem and checks `0 = 1`. With no dependency cache, strict rejects.
Running without strict creates a dependency cache; the subsequent strict run
currently succeeds. This is a confirmed unsafe acceptance, not an expected
negative to relabel and not a legitimate mathematical example.

```sh
litex -strict -r examples/module_manager/strict_cache_policy
litex -r examples/module_manager/strict_cache_policy
litex -strict -r examples/module_manager/strict_cache_policy
```

Run this sequence from a fresh copy without a dependency cache. Expected exits
are `1, 0, 1`; observed exits are `1, 0, 0`. The focused Rust regression creates
and cleans its own temporary fixture and keeps the last rejection assertion:

```sh
cargo test --release --offline run_module::strict_cache_tests::strict_import_cannot_replay_a_non_strict_trusted_theorem -- --exact --nocapture
```

The current cache stores definitions without strict-validation provenance.
`src/run_module/import_kb.rs::try_finish_import_from_kb` installs these definitions
without checking the launch mode. A reviewable proposed guard returns the
existing `ImportKbHit::Miss` under strict, so the existing cold path verifies
the source again. It changes no AST/Runtime field or cache format, but strict
imports become slower. **The guard is not applied; concrete cache authorization
is pending.** The alternative is a separately designed cache certificate that
covers verifier/version/mode and transitive dependencies, not merely a boolean
on the root cache.

Owner: maintainer chooses cold strict verification or a certified-cache design;
Codex then implements and runs cold/warm, direct/transitive import, trust,
valid import and error-forwarding controls. Do not weaken the red regression.

[Acceptance, raw evidence and exact proposed patch](../../../tests/tooling/acceptance/conversation-closeout-retest-2026-10-04.md#cache).
Canonical route: [LEG29](../../../plan/src收尾总清单.md#leg29).
