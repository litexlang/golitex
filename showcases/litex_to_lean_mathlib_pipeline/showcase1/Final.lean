import Adapter

/-!
# Native final theorem

The proposition after `:` is ordinary Lean/Mathlib mathematics. It does not
mention `Litex.Same`, `Litex.sum`, or any compiler-generated declaration.

The explicit `bridge` parameter is the Adapter certificate requested by this
showcase. Keeping it explicit is important: `Adapter.lean` defines and uses the
certificate interface, but does not postulate a value of it. The proof body
then cites the Adapter theorem that genuinely consumes the generated Litex
proof.
-/

theorem firstHundredPositiveOddIntegersSum
    (bridge : OddSumPipeline.IntegerSameEqBridge) :
    ∑ k ∈ Finset.Icc (1 : ℤ) 100, (2 * k - 1) = 10000 := by
  exact OddSumPipeline.sumFirstOddsNative bridge 100 (by norm_num)
