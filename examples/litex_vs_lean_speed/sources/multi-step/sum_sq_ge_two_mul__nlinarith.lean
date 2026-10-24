import Mathlib

example : ∀ x y : Real, 2*x*y ≤ x^2 + y^2 := by intro x y; nlinarith [sq_nonneg (x-y)]
