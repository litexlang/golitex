theorem order_add_positive_of_positive_nonnegative
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (ha : 0 < a)
    (hb : 0 ≤ b) : 0 < a + b := by
  exact add_pos_of_pos_of_nonneg ha hb
