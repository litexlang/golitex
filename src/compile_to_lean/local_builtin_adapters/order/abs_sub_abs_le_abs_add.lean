theorem order_abs_sub_abs_le_abs_add
    (x y : ℝ)
    (_hxR : x ∈ (Set.univ : Set ℝ))
    (_hyR : y ∈ (Set.univ : Set ℝ)) : |x| - |y| ≤ |x + y| := by
  simpa using abs_sub_abs_le_abs_sub x (-y)
