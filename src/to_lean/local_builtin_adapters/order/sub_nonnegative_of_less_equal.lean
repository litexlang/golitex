theorem order_sub_nonnegative_of_less_equal
    (u v : ℝ)
    (_huR : u ∈ (Set.univ : Set ℝ))
    (_hvR : v ∈ (Set.univ : Set ℝ))
    (h : v ≤ u) : 0 ≤ u - v := by
  exact sub_nonneg.mpr h
