theorem set_union_subset
    {α : Type*}
    (A B S : Set α)
    (_hA : True)
    (_hB : True)
    (_hS : True)
    (hA : A ⊆ S)
    (hB : B ⊆ S) : A ∪ B ⊆ S := by
  exact Set.union_subset hA hB
