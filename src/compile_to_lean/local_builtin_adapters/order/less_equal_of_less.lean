theorem order_less_equal_of_less
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (h : a < b) : a ≤ b := by
  exact le_of_lt h
