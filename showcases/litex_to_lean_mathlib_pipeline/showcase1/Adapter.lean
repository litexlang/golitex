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

This first adapter keeps the generated heterogeneous conclusion visible; the
next theorem eliminates it through Core's public numeric observation API. -/
theorem sumFirstOdds (n : ℤ) (oneLeN : (1 : ℤ) ≤ n) :
    Litex.Same
      (oddSum n)
      ((((n : ℚ) ^ (2 : ℤ) : ℚ) : ℂ)) := by
  unfold oddSum
  apply __Compiler_main.sum_first_odds n
  exact Litex.OrderBridge.leOfComplexReals (by exact_mod_cast oneLeN)

/-- Turn the actual generated theorem into ordinary Mathlib equality.

`Litex.Same.intComplexEq` is the general, axiom-free Core eliminator: it reads
the numeric observations already retained by a checked `Litex.Same` proof.
This adapter contains no second proof of the odd-sum identity. -/
theorem sumFirstOddsNative
    (n : ℤ)
    (oneLeN : (1 : ℤ) ≤ n) :
    ∑ k ∈ Finset.Icc (1 : ℤ) n, (2 * k - 1) = n ^ 2 := by
  have generated :=
    __Compiler_main.sum_first_odds n
      (Litex.OrderBridge.leOfComplexReals (by exact_mod_cast oneLeN))
  have observedComplexEq :
      ((Litex.sum (1 : ℤ) n __Compiler_main.kth_odd : ℤ) : ℂ) =
        ((((n : ℚ) ^ (2 : ℤ) : ℚ) : ℂ)) :=
    Litex.Same.intComplexEq generated
  have exactComplexEq :
      ((Litex.sum (1 : ℤ) n __Compiler_main.kth_odd : ℤ) : ℂ) =
        ((n ^ 2 : ℤ) : ℂ) := by
    calc
      ((Litex.sum (1 : ℤ) n __Compiler_main.kth_odd : ℤ) : ℂ) =
          ((((n : ℚ) ^ (2 : ℤ) : ℚ) : ℂ)) := observedComplexEq
      _ = ((n ^ 2 : ℤ) : ℂ) := by norm_cast
  have exactCarrierEq :
      Litex.sum (1 : ℤ) n __Compiler_main.kth_odd = n ^ 2 :=
    by exact_mod_cast exactComplexEq
  simpa [Litex.sum, Litex.integerRangeSum, __Compiler_main.kth_odd] using
    exactCarrierEq

end OddSumPipeline
