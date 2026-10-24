import Mathlib

example : ∀ x : Real, 0 < x^2 + 1 := by intro x; positivity
