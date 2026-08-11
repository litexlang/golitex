theorem order_sub_positive_of_less
    (u v : ℝ)
    (_huR : u ∈ (Set.univ : Set ℝ))
    (_hvR : v ∈ (Set.univ : Set ℝ))
    (h : v < u) : 0 < u - v := by
  exact sub_pos.mpr h
