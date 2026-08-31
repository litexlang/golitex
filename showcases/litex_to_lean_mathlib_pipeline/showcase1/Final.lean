import Adapter

/-!
# Native final theorem

The proposition after `:` is ordinary Lean/Mathlib mathematics. It does not
mention `Litex.Same`, `Litex.sum`, or any compiler-generated declaration.

The statement is deliberately unaware that Litex exists. Only the proof body
cites the handwritten Adapter, whose proof in turn cites generated Litex code.
-/

theorem firstHundredPositiveOddIntegersSum :
    ∑ k ∈ Finset.Icc (1 : ℤ) 100, (2 * k - 1) = 10000 := by
  exact OddSumPipeline.sumFirstOddsNative 100 (by norm_num)
