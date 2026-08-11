theorem set_union_empty_left
    {α : Type*}
    (A : Set α)
    (_hA : True) : ∅ ∪ A = A := by
  exact Set.empty_union A
