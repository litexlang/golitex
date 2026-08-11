theorem set_union_nonempty_right
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True)
    (hB : B.Nonempty) : (A ∪ B).Nonempty := by
  rcases hB with ⟨x, hx⟩
  exact ⟨x, Set.mem_union_right A hx⟩
