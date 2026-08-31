import Adapter

/-!
# Native final target

The public theorem must be ordinary Lean/Mathlib mathematics and must not
mention `Litex.Same`, `Litex.sum`, generated names, or adapter wrappers in its
statement:

```lean
theorem firstHundredPositiveOddIntegersSum :
    ∑ k ∈ Finset.Icc (1 : ℤ) 100, (2 * k - 1) = 10000 := by
  exact OddSumPipeline.sumFirstOddsNative
    Litex.integerSameEqBridge 100 (by norm_num)
```

The theorem is intentionally not declared yet. `Adapter.lean` proves the
conditional native result, but the repository does not yet contain the
soundly constructed `Litex.integerSameEqBridge` certificate shown above.
Declaring the theorem before that certificate exists would require an axiom,
a proof hole, or an independent duplicate proof, none of which demonstrates
the requested Litex-to-native pipeline.
-/
