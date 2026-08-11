theorem order_max_monotone
    (a b c d : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (_hcR : c ∈ (Set.univ : Set ℝ))
    (_hdR : d ∈ (Set.univ : Set ℝ))
    (hac : a ≤ c)
    (hbd : b ≤ d) : max a b ≤ max c d := by
  exact max_le_max hac hbd
