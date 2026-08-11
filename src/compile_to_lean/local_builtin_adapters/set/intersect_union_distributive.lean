theorem set_intersect_union_distributive
    {α : Type*}
    (A B C : Set α)
    (_hA : True)
    (_hB : True)
    (_hC : True) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  exact Set.inter_union_distrib_left A B C
