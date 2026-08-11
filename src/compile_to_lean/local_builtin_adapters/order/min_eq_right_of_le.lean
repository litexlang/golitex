theorem order_min_eq_right_of_le
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (h : b ≤ a) : min a b = b := by
  exact min_eq_right h
