theorem order_add_lt_add_of_lt_of_le
    (a b c d : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (_hcR : c ∈ (Set.univ : Set ℝ))
    (_hdR : d ∈ (Set.univ : Set ℝ))
    (hab : a < b)
    (hcd : c ≤ d) : a + c < b + d := by
  exact add_lt_add_of_lt_of_le hab hcd
