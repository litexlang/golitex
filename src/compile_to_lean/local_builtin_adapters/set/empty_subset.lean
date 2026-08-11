theorem set_empty_subset
    {α : Type*}
    (A : Set α)
    (_hA : True) : (∅ : Set α) ⊆ A := by
  exact Set.empty_subset A
