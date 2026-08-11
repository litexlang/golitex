theorem order_self_le_abs
    (x : ℝ)
    (_hxR : x ∈ (Set.univ : Set ℝ)) : x ≤ |x| := by
  exact le_abs_self x
