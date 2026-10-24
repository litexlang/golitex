import Mathlib

example : ∀ x y : Real, 2*x = 2*y → x = y := by intro x y h; linarith
