theorem order_min_monotone
    (a b c d : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (_hcR : c ∈ (Set.univ : Set ℝ))
    (_hdR : d ∈ (Set.univ : Set ℝ))
    (hac : a ≤ c)
    (hbd : b ≤ d) : min a b ≤ min c d := by
  exact min_le_min hac hbd
