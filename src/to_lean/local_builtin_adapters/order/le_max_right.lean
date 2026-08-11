theorem order_le_max_right
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ)) : b ≤ max a b := by
  exact le_max_right a b
