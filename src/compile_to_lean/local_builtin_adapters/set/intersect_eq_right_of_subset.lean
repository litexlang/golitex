theorem set_intersect_eq_right_of_subset
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True)
    (h : B ⊆ A) : A ∩ B = B := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.2
  · intro x hx
    exact ⟨h hx, hx⟩
