import Mathlib

example : ∀ x : Real, 0 < x → 0 < x/(x+1) := by
  intro x hx
  have h1 : (0 : Real) < x + 1 := by linarith
  exact div_pos hx h1
