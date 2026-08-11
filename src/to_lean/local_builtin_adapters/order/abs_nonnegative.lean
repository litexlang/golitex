theorem order_abs_nonnegative
    (x : ℝ)
    (_hxR : x ∈ (Set.univ : Set ℝ)) : 0 ≤ |x| := by
  exact abs_nonneg x
