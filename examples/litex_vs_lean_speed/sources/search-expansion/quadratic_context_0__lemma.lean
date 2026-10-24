import Mathlib

set_option linter.unusedVariables false

example : ∀ (x y : ℝ), 2*x*y ≤ x^2+y^2 := by
  intro x y
  exact two_mul_le_add_sq x y
