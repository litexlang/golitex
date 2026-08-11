theorem order_neg_abs_le
    (x : ℝ)
    (_hxR : x ∈ (Set.univ : Set ℝ)) : (-1 : ℝ) * |x| ≤ x := by
  simpa using neg_abs_le x
