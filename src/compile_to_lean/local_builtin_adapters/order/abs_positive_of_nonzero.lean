theorem order_abs_positive_of_nonzero
    (x : ℝ)
    (_hxR : x ∈ (Set.univ : Set ℝ))
    (hx : x ≠ 0) : 0 < |x| := by
  exact abs_pos.mpr hx
