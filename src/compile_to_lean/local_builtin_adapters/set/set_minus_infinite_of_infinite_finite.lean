theorem set_set_minus_infinite_of_infinite_finite
    {α : Type*}
    (X S : Set α)
    (_hX : True)
    (_hS : True)
    (hX : ¬ X.Finite)
    (hS : S.Finite) : ¬ (X \ S).Finite := by
  classical
  intro hDifference
  apply hX
  apply (hDifference.union hS).subset
  intro x hxX
  by_cases hxS : x ∈ S
  · exact Or.inr hxS
  · exact Or.inl ⟨hxX, hxS⟩
