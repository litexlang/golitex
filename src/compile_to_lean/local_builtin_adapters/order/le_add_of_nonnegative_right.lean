theorem order_le_add_of_nonnegative_right
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (hb : 0 ≤ b) : a ≤ a + b := by
  linarith only [hb]
