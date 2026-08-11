theorem order_add_nonnegative
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (ha : 0 ≤ a)
    (hb : 0 ≤ b) : 0 ≤ a + b := by
  exact add_nonneg ha hb
