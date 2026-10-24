import Mathlib

set_option linter.unusedVariables false

example : ∀ (x y z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 : ℝ), 0 ≤ z0 → 0 ≤ z1 → 0 ≤ z2 → 0 ≤ z3 → 0 ≤ z4 → 0 ≤ z5 → 0 ≤ z6 → 0 ≤ z7 → 0 ≤ z8 → 0 ≤ z9 → 0 ≤ z10 → 0 ≤ z11 → 0 ≤ z12 → 0 ≤ z13 → 0 ≤ z14 → 0 ≤ z15 → 0 ≤ z16 → 0 ≤ z17 → 0 ≤ z18 → 0 ≤ z19 → 0 ≤ z20 → 0 ≤ z21 → 0 ≤ z22 → 0 ≤ z23 → 2*x*y ≤ x^2+y^2 := by
  intro x y z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23
  exact two_mul_le_add_sq x y
