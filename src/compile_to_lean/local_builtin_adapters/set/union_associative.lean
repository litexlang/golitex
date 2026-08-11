theorem set_union_associative
    {α : Type*}
    (A B C : Set α)
    (_hA : True)
    (_hB : True)
    (_hC : True) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  exact Set.union_assoc A B C
