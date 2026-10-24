import Mathlib

set_option linter.unusedVariables false

example : ∀ (u : ℕ → ℚ) (c : ℚ), (∑ k ∈ Finset.range 64, (u (k+1) + c)) = (∑ k ∈ Finset.range 64, u (k+1)) + 64*c := by
  intro u c
  simp [Finset.sum_add_distrib]
