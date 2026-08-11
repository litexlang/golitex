theorem nonzero_mul
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (ha : a ≠ 0)
    (hb : b ≠ 0) : a * b ≠ 0 := by
  exact mul_ne_zero ha hb
