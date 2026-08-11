theorem set_intersect_subset_right
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True) : A ∩ B ⊆ B := by
  intro x hx
  exact hx.2
