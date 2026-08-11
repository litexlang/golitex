theorem order_min_absorb_max_left
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ)) : min a (max a b) = a := by
  exact min_eq_left (le_max_left a b)
