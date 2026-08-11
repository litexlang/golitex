theorem order_max_absorb_min_left
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ)) : max a (min a b) = a := by
  exact max_eq_left (min_le_left a b)
