import Mathlib

set_option linter.unusedVariables false

example : ∀ (u : ℕ → ℚ) (c : ℚ), (∑ k ∈ Finset.range 64, (u (k+1) + c)) = (∑ k ∈ Finset.range 64, u (k+1)) + 64*c := by
  intro u c
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  ring
