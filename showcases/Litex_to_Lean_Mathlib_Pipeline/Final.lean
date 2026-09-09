import Adapter

/-- Native Lean baseline: the proof is written directly as an induction. -/
theorem sum_odd_nat (n : ℕ) :
    ∑ k ∈ Finset.range n, (2 * (k + 1) - 1) = n ^ 2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [Nat.mul_add]
      ring

/-- The same native statement, obtained from the checked Litex theorem. -/
theorem sum_odd_nat_via_litex (n : ℕ) :
    ∑ k ∈ Finset.range n, (2 * (k + 1) - 1) = n ^ 2 := by
  exact Adapter.sumOddNatViaLitex n
