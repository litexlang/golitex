theorem set_intersect_eq_left_of_subset
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True)
    (h : A ⊆ B) : A ∩ B = A := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.1
  · intro x hx
    exact ⟨hx, h hx⟩
