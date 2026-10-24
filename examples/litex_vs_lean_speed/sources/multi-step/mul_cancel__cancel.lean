import Mathlib

example : ∀ x y : Real, 2*x = 2*y → x = y := by intro x y h; exact mul_left_cancel₀ (by norm_num : (2:Real) ≠ 0) h
