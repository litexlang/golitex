theorem order_mul_positive
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (ha : 0 < a)
    (hb : 0 < b) : 0 < a * b := by
  exact mul_pos ha hb
