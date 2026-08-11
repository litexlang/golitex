theorem order_min_idempotent
    (a : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ)) : min a a = a := by
  exact min_self a
