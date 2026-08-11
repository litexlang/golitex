theorem order_max_eq_right_of_le
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (h : a ≤ b) : max a b = b := by
  exact max_eq_right h
