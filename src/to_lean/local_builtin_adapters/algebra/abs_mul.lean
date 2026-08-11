theorem algebra_abs_mul
    (x y : ℝ)
    (_hxR : x ∈ (Set.univ : Set ℝ))
    (_hyR : y ∈ (Set.univ : Set ℝ)) : |x * y| = |x| * |y| := by
  exact abs_mul x y
