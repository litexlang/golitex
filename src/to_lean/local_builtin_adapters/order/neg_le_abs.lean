theorem order_neg_le_abs
    (x : ℝ)
    (_hxR : x ∈ (Set.univ : Set ℝ)) : (-1 : ℝ) * x ≤ |x| := by
  simpa using neg_le_abs x
