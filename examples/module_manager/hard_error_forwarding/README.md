# Mounted hard-error forwarding

`litex -strict -r examples/module_manager/hard_error_forwarding` exits 1 and
preserves the dependency's `Runtime(InvalidArguments(...))` forbidden-trust
message. It must not replace that hard error with `FailToImport`, and the root
file must not execute. A run without `-strict` succeeds.

The same forwarding applies to root exports, file-prefix mounting and REPL
mounting. A soft failed fact (`1 = 2`) still becomes `FailToImport`; the focused
Rust regression covers that adjacent boundary. InternalBug uses the same
unchanged Runtime-error forwarding path and keeps its explicit Litex-bug text.

After a non-strict run creates a dependency cache, strict now rechecks the
source and preserves the same forbidden-trust error. The separate cache
bypass is closed in [strict_cache_policy](../strict_cache_policy/README.md).
The geometry authoring issue is also closed by explicit `release obj def` in
its original module; it required no module-owner lookup change.

[Current evidence](../../../tests/tooling/acceptance/conversation-clarifications-2026-10-04.md).
[Historical error-forwarding evidence](../../../tests/tooling/acceptance/conversation-closeout-retest-2026-10-04.md).
