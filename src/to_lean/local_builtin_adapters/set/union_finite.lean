theorem set_union_finite
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True)
    (hA : A.Finite)
    (hB : B.Finite) : (A ∪ B).Finite := by
  exact hA.union hB
