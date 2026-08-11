theorem order_sub_le_of_le_of_nonnegative
    (a b c : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (_hcR : c ∈ (Set.univ : Set ℝ))
    (hab : a ≤ b)
    (hc : 0 ≤ c) : a - c ≤ b := by
  linarith only [hab, hc]
