theorem set_intersect_commutative
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True) : A ∩ B = B ∩ A := by
  exact Set.inter_comm A B
