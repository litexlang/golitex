import Mathlib

set_option linter.unusedVariables false

example : ∀ (u : ℕ → ℚ) (c : ℚ), (∑ k ∈ Finset.range 128, (u (k+1) + c)) = (∑ k ∈ Finset.range 128, u (k+1)) + 128*c := by
  intro u c
  simp [Finset.sum_add_distrib]
