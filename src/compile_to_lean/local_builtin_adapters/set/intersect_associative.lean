theorem set_intersect_associative
    {α : Type*}
    (A B C : Set α)
    (_hA : True)
    (_hB : True)
    (_hC : True) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  exact Set.inter_assoc A B C
