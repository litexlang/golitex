# Builtin real least-upper-bound conclusion cannot pass WD

Task: broad kernel gate during classified contra work, 2026-10-03.
Scope: ByThmStmt / native builtin theorem conclusion WD.
Ownership: category 2 candidate; Codex investigates the existing builtin
predicate-signature owner before deciding a bounded repair. Cause locality
is not yet established.

```litex
release thm real_least_upper_bound_exists({0}, 1)
exist L R st {$is_real_least_upper_bound({0}, L)}
```

The catalogue test expects this existing positive tracer to pass. Both frozen
before and current binaries reject it. The first failure is
`conclusion_well_defined -> predicate_signature -> undefined_predicate`,
for `is_real_least_upper_bound`; the final citation also fails WD.
Do not bypass WD or manufacture a proposition declaration to make it green.
Next action: reconcile the native theorem's declared output with the existing
builtin predicate interface and its precise argument-domain checks.

Exact input/output and full-kernel failure:
[journal](../../proof_journals/by_contra_full_kernel_failures_2026-10-02.json).
Original positive tracer remains under `examples/stmt_nodes/release_and_expand/builtin_thm/`.
