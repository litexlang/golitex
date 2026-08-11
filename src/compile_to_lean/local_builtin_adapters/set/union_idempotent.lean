theorem set_union_idempotent
    {α : Type*}
    (A : Set α)
    (_hA : True) : A ∪ A = A := by
  exact Set.union_self A
