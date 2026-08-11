theorem order_abs_eq_neg_of_nonpositive
    (x : ℝ)
    (_hxR : x ∈ (Set.univ : Set ℝ))
    (hx : x ≤ 0) : |x| = (-1 : ℝ) * x := by
  simpa using abs_of_nonpos hx
