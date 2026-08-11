theorem order_max_commutative
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ)) : max a b = max b a := by
  exact max_comm a b
