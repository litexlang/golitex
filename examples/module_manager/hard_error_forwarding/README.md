# Mounted hard-error forwarding

On a fresh fixture without a dependency cache,
`litex -strict -r examples/module_manager/hard_error_forwarding` exits 1 and
preserves the dependency's `Runtime(InvalidArguments(...))` forbidden-trust
message. It must not replace that hard error with `FailToImport`, and the root
file must not execute. A run without `-strict` succeeds.

The same forwarding applies to root exports, file-prefix mounting and REPL
mounting. A soft failed fact (`1 = 2`) still becomes `FailToImport`; the focused
Rust regression covers that adjacent boundary. InternalBug uses the same
unchanged Runtime-error forwarding path and keeps its explicit Litex-bug text.

This tracer does not repair the underlying cross-file geometry WD issue.

After a non-strict run creates a dependency cache, the strict run currently
bypasses this source check. That separate confirmed defect is recorded in
[strict_cache_policy](../strict_cache_policy/README.md); the proposed cold
strict verification guard awaits concrete cache authorization. Do not use a
warmed version of this fixture as evidence that error forwarding is broken.
[This turn's evidence](../../../tests/tooling/acceptance/conversation-closeout-retest-2026-10-04.md).
