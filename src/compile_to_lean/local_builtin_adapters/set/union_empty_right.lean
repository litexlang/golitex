theorem set_union_empty_right
    {α : Type*}
    (A : Set α)
    (_hA : True) : A ∪ ∅ = A := by
  exact Set.union_empty A
