theorem set_union_commutative
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True) : A ∪ B = B ∪ A := by
  exact Set.union_comm A B
