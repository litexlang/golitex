import Generated

/-!
This handwritten module is the only adapter between compiler-owned names and
the theorem used by `Final.lean`. It must cite the generated declaration; it
must not silently prove the odd-sum identity again with an independent Mathlib
induction.
-/

namespace OddSumPipeline

/-- The exact integer sum represented by the generated Litex function. -/
noncomputable def oddSum (n : ℤ) : ℤ :=
  Litex.sum (1 : ℤ) n __Compiler_main.kth_odd

/-- Re-export the generated theorem with a native Lean order premise.

The conclusion intentionally remains `Litex.Same`: the current public ABI has
no proved eliminator from this heterogeneous equality to a native integer
equality. -/
theorem sumFirstOdds (n : ℤ) (oneLeN : (1 : ℤ) ≤ n) :
    Litex.Same
      (oddSum n)
      ((((n : ℚ) ^ (2 : ℤ) : ℚ) : ℂ)) := by
  unfold oddSum
  apply __Compiler_main.sum_first_odds n
  exact Litex.OrderBridge.leOfComplexReals (by exact_mod_cast oneLeN)

/-!
## Adapter-local prototype: `Litex.Same` to native `Eq`

`IntegerSameEqBridge` is deliberately a proof-carrying interface, not an
axiom and not an alternative definition of equality. It records the exact
eliminator that Core would have to prove before an unconditional native
downstream theorem can be sound.
-/

/-- A proposed elimination certificate for integer-valued semantic equality.

No value of this structure is postulated here. Keeping the prototype local to
the adapter makes its eventual Core contract reviewable before it becomes part
of the shared ABI. -/
structure IntegerSameEqBridge : Prop where
  toEq {left right : ℤ} :
    Litex.Same left (right : ℂ) → left = right

/-- Conditional end-to-end result: a proved `IntegerSameEqBridge` turns the
actual generated theorem into an ordinary Mathlib equality. The odd-sum
induction is not repeated here. -/
theorem sumFirstOddsNative
    (bridge : IntegerSameEqBridge)
    (n : ℤ)
    (oneLeN : (1 : ℤ) ≤ n) :
    ∑ k ∈ Finset.Icc (1 : ℤ) n, (2 * k - 1) = n ^ 2 := by
  have generated :=
    __Compiler_main.sum_first_odds n
      (Litex.OrderBridge.leOfComplexReals (by exact_mod_cast oneLeN))
  have renderedAsInteger :
      Litex.Same
        ((((n : ℚ) ^ (2 : ℤ) : ℚ) : ℂ))
        (((n ^ 2 : ℤ) : ℂ)) :=
    Litex.Same.ofEq (by norm_cast)
  have exactCarrierSame :
      Litex.Same
        (Litex.sum (1 : ℤ) n __Compiler_main.kth_odd)
        (((n ^ 2 : ℤ) : ℂ)) :=
    Litex.Same.trans generated renderedAsInteger
  have exactCarrierEq :
      Litex.sum (1 : ℤ) n __Compiler_main.kth_odd = n ^ 2 :=
    bridge.toEq exactCarrierSame
  simpa [Litex.sum, Litex.integerRangeSum, __Compiler_main.kth_odd] using
    exactCarrierEq

end OddSumPipeline
