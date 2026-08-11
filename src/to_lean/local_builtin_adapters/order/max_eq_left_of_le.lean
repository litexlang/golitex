theorem order_max_eq_left_of_le
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (h : b ≤ a) : max a b = a := by
  exact max_eq_left h
