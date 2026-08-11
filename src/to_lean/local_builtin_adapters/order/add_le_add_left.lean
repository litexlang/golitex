theorem order_add_le_add_left
    (u a b : ℝ)
    (_huR : u ∈ (Set.univ : Set ℝ))
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (h : a ≤ b) : u + a ≤ u + b := by
  linarith only [h]
