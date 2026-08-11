theorem order_abs_add_le
    (x y : ℝ)
    (_hxR : x ∈ (Set.univ : Set ℝ))
    (_hyR : y ∈ (Set.univ : Set ℝ)) : |x + y| ≤ |x| + |y| := by
  exact abs_add_le x y
