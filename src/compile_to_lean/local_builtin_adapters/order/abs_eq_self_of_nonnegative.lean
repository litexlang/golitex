theorem order_abs_eq_self_of_nonnegative
    (x : ℝ)
    (_hxR : x ∈ (Set.univ : Set ℝ))
    (hx : 0 ≤ x) : |x| = x := by
  exact abs_of_nonneg hx
