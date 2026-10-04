# Strict import cache policy — repaired 2026-10-04

Task: conversation clarification and retest. Scope: non-strict import-cache
replay under strict mode. Label: `kernel_problem`. The maintainer confirmed
that strict must reject every user trust statement. The previously proposed
strict-to-Miss guard is now applied; no cache format or state field changed.

The dependency deliberately uses trust to declare `0 = 1`; the root releases
that theorem and checks `0 = 1`. Previously, a cache created by ordinary mode
let strict accept this false theorem. Strict now rechecks the dependency source.

```sh
litex -strict -r examples/module_manager/strict_cache_policy
litex -r examples/module_manager/strict_cache_policy
litex -strict -r examples/module_manager/strict_cache_policy
```

From a fresh copy without dependency caches, expected and observed exits are
`1, 0, 1`. The original false-theorem rejection assertion remains unchanged.

`src/run_module/import_kb.rs::try_finish_import_from_kb` now returns the existing
`ImportKbHit::Miss` under strict. Strict imports therefore recheck dependencies
even when an ordinary cache exists. Ordinary imports retain actual cache hits.

Direct and transitive trusted false theorems reject in cold and warm strict
runs. A valid dependency passes both modes: ordinary warm execution skips its
source, while strict warm execution rechecks it. All 26 module regressions pass.
These Rust fixtures create and clean their own temporary modules.

```sh
cargo test --release --offline run_module::strict_cache_tests
```

[Current acceptance and raw evidence](../../../tests/tooling/acceptance/conversation-clarifications-2026-10-04.md).
[Historical defect and exact proposed patch](../../../tests/tooling/acceptance/conversation-closeout-retest-2026-10-04.md#cache).
Canonical route: [LEG29](../../../plan/src收尾总清单.md#leg29).
