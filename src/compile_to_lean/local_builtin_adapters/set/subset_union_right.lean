theorem set_subset_union_right
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True) : B ⊆ A ∪ B := by
  intro x hx
  exact Or.inr hx
