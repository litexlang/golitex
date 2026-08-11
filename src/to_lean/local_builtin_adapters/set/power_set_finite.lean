theorem set_power_set_finite
    {α : Type*}
    (A : Set α)
    (_hA : True)
    (hA : A.Finite) : (Set.powerset A).Finite := by
  exact hA.powerset
