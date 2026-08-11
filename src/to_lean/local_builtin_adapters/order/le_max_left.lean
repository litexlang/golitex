theorem order_le_max_left
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ)) : a ≤ max a b := by
  exact le_max_left a b
