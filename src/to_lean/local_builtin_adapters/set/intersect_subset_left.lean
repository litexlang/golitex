theorem set_intersect_subset_left
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True) : A ∩ B ⊆ A := by
  intro x hx
  exact hx.1
