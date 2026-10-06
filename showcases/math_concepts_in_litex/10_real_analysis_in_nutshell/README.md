# Real Analysis in a Nutshell

This standalone showcase expresses epsilon-tail convergence, includes proofs
of constant-sequence convergence and uniqueness of sequence limits, and uses
that existence-and-uniqueness result to define a canonical `lim` selector.
The complete Litex file and registered module passed strict release
verification on 2026-10-01.

```bash
target/release/litex -strict -r showcases/math_concepts_in_litex/10_real_analysis_in_nutshell
cd lean
lake env lean ../showcases/math_concepts_in_litex/10_real_analysis_in_nutshell/same_math_in_lean.lean
```

The Lean comparison defines closeness as the actual real inequality
`|a n - L| < ε` and derives uniqueness with `Nat.max` and the triangle
inequality. The published Litex file contains no direct trust or local axiom.

The sequence carrier is written explicitly as `fn(index N+) R`, preserving
the original one-based indexing. The constant proof establishes the tail
before choosing its witness. Uniqueness uses `n1 + n2` as a common tail index,
then explicit absolute-value and triangle-inequality steps. All five formerly
failing statements now pass; see
[`和showcase有关.md`](../../../plan/迁移的plan/和showcase有关.md) for evidence.
The Lean comparison was not rerun.

This module itself stops at sequence-limit existence, uniqueness, and safe
selection. The broader calculus/real-analysis direction may later grow through
Rolle and MVT, then stops; uniform convergence, integration, measure theory,
and functional analysis are separate slices, not completion requirements here.

## Current callable interfaces

Constant sequences use the named function template `\constant_sequence<c>` with value `c` at every positive index. The epsilon-tail proof and unique limit selector remain constructive.
