# Real Analysis in a Nutshell

This standalone showcase expresses epsilon-tail convergence, includes proofs
of constant-sequence convergence and uniqueness of sequence limits, and uses
that existence-and-uniqueness result to define a canonical `lim` selector.
Those proofs remain blocked by the current migration; they are not yet a
verified complete module.

```bash
target/release/litex -strict -r showcases/math_concepts_in_litex/10_real_analysis_in_nutshell
cd lean
lake env lean ../showcases/math_concepts_in_litex/10_real_analysis_in_nutshell/same_math_in_lean.lean
```

The Lean comparison defines closeness as the actual real inequality
`|a n - L| < ε` and derives uniqueness with `Nat.max` and the triangle
inequality. The published Litex file contains no direct trust or local axiom.

The equality-bridge recheck still reports five failed Litex statements in the
constant-limit, uniqueness, and selector chain. See
[`和showcase有关.md`](../../../plan/迁移的plan/和showcase有关.md) for the attempted
proofs and current diagnostics. The Lean comparison was not rerun in this cleanup.

This module itself stops at sequence-limit existence, uniqueness, and safe
selection. The broader calculus/real-analysis direction may later grow through
Rolle and MVT, then stops; uniform convergence, integration, measure theory,
and functional analysis are separate slices, not completion requirements here.
