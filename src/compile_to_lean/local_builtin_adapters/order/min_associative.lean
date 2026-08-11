theorem order_min_associative
    (a b c : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (_hcR : c ∈ (Set.univ : Set ℝ)) :
    min (min a b) c = min a (min b c) := by
  exact min_assoc a b c
