# Finite-set cardinality comparison loses a numeric carrier

Task: broad kernel gate during classified contra work, 2026-10-03.
Scope: Fact / finite_set_size result carrier and comparison WD.
Ownership: category 1 versus category 2 remains provisional. Diagnose the
numeric-result carrier before choosing an authoring bridge or local Rust rule.

```litex
have A set = {1, 2}
have B set = {1}
have fn f(x A) B = 1
trust $surjective(A, B, f)
finite_set_size(B) <= finite_set_size(A)
```

This exact existing kernel control runs outside strict mode because its setup
contains trust. All four setup statements pass in frozen before and current
binaries; the final comparison fails in both. Its comparison WD requires
`finite_set_size(B) $in R`, whose search_proof fails. The test expects the
finite-cardinality inequality. The trust line is preserved historical input,
not a repair or a newly accepted proof debt.

Next action: check finite-set alias evidence and the builtin cardinality's
numeric codomain. Preserve the real-comparison domain obligation; do not
weaken comparison WD or add trust to the desired conclusion.

Exact sources/results and phase:
[journal](../../proof_journals/by_contra_full_kernel_failures_2026-10-02.json).
