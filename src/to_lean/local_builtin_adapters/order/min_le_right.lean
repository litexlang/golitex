theorem order_min_le_right
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ)) : min a b ≤ b := by
  exact min_le_right a b
