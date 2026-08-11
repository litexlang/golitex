theorem set_subset_union_left
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True) : A ⊆ A ∪ B := by
  intro x hx
  exact Or.inl hx
