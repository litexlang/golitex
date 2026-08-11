theorem order_max_idempotent
    (a : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ)) : max a a = a := by
  exact max_self a
