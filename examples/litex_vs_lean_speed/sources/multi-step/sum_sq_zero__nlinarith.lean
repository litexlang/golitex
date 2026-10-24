import Mathlib

example : ∀ x y : Real, x^2 + y^2 = 0 → x = 0 ∧ y = 0 := by
  intro x y h
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
