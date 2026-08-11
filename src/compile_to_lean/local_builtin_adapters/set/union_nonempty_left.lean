theorem set_union_nonempty_left
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True)
    (hA : A.Nonempty) : (A ∪ B).Nonempty := by
  rcases hA with ⟨x, hx⟩
  exact ⟨x, Set.mem_union_left B hx⟩
