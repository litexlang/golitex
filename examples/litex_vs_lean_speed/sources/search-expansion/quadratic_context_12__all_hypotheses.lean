import Mathlib

set_option linter.unusedVariables false

example : ∀ (x y z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 : ℝ), 0 ≤ z0 → 0 ≤ z1 → 0 ≤ z2 → 0 ≤ z3 → 0 ≤ z4 → 0 ≤ z5 → 0 ≤ z6 → 0 ≤ z7 → 0 ≤ z8 → 0 ≤ z9 → 0 ≤ z10 → 0 ≤ z11 → 2*x*y ≤ x^2+y^2 := by
  intro x y z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  nlinarith [sq_nonneg (x-y)]
