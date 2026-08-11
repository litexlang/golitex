theorem set_power_set_membership_of_subset
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True)
    (h : A ⊆ B) : A ∈ Set.powerset B := by
  exact h
