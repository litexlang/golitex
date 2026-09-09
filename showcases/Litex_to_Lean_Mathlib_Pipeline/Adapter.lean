import Generated

/-! The handwritten interface from generated Litex evidence to native Mathlib. -/

namespace Adapter

/-- Export the generated theorem as ordinary Mathlib equality. -/
theorem sumFirstOddsNative
    (n : ℤ)
    (oneLeN : (1 : ℤ) ≤ n) :
    ∑ k ∈ Finset.Icc (1 : ℤ) n, (2 * k - 1) = n ^ 2 := by
  have generated :=
    __Compiler_main.sum_first_odds n
      (Litex.OrderBridge.leOfComplexReals (by exact_mod_cast oneLeN))
  have exactComplexEq :
      ((Litex.sum (1 : ℤ) n __Compiler_main.kth_odd : ℤ) : ℂ) =
        ((n ^ 2 : ℤ) : ℂ) := by
    calc
      ((Litex.sum (1 : ℤ) n __Compiler_main.kth_odd : ℤ) : ℂ) =
          ((((n : ℚ) ^ (2 : ℤ) : ℚ) : ℂ)) :=
        Litex.Same.intComplexEq generated
      _ = ((n ^ 2 : ℤ) : ℂ) := by norm_cast
  exact_mod_cast exactComplexEq

/-! Convert the checked Litex integer interval sum into the native
    `Nat`/`Finset.range` interface used by the comparison theorem. -/
theorem sumOddNatViaLitex
    (n : ℕ) :
    ∑ k ∈ Finset.range n, (2 * (k + 1) - 1) = n ^ 2 := by
  have hBridge :
      ((∑ k ∈ Finset.range n, (2 * (k + 1) - 1) : ℕ) : ℤ) =
        ∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (2 * k - 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, Nat.cast_add]
        have hIcc :
            insert ((n : ℤ) + 1) (Finset.Icc (1 : ℤ) (n : ℤ)) =
              Finset.Icc (1 : ℤ) ((n : ℤ) + 1) := by
          exact Finset.insert_Icc_right_eq_Icc_add_one (by omega)
        have hIcc' :
            insert ((n : ℤ) + 1) (Finset.Icc (1 : ℤ) (n : ℤ)) =
              Finset.Icc (1 : ℤ) ((n + 1 : ℕ) : ℤ) := by
          simpa using hIcc
        rw [← hIcc', Finset.sum_insert]
        · rw [ih]
          norm_num
          ring
        · simp
  cases n with
  | zero => simp
  | succ n =>
      have hInt := sumFirstOddsNative (n.succ : ℤ) (by omega)
      have hNat :
          ((∑ k ∈ Finset.range n.succ, (2 * (k + 1) - 1) : ℕ) : ℤ) =
            ((n.succ ^ 2 : ℕ) : ℤ) := by
        rw [hBridge, hInt]
        norm_num
      exact_mod_cast hNat

end Adapter
