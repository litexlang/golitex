theorem order_abs_sub_le_sum
    (x y : ℝ)
    (_hxR : x ∈ (Set.univ : Set ℝ))
    (_hyR : y ∈ (Set.univ : Set ℝ)) : |x - y| ≤ |x| + |y| := by
  simpa using abs_sub_le x 0 y
