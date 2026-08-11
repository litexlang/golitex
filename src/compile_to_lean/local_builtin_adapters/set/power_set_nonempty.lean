theorem set_power_set_nonempty
    {α : Type*}
    (A : Set α)
    (_hA : True) : (Set.powerset A).Nonempty := by
  refine ⟨∅, ?_⟩
  exact Set.empty_subset A
