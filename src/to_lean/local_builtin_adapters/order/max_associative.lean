theorem order_max_associative
    (a b c : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (_hcR : c ∈ (Set.univ : Set ℝ)) :
    max (max a b) c = max a (max b c) := by
  exact max_assoc a b c
