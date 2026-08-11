theorem set_set_minus_intersect_de_morgan
    {α : Type*}
    (A B C : Set α)
    (_hA : True)
    (_hB : True)
    (_hC : True) : A \ (B ∩ C) = (A \ B) ∪ (A \ C) := by
  exact Set.diff_inter
