theorem set_set_minus_finite_left
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True)
    (hA : A.Finite) : (A \ B).Finite := by
  apply hA.subset
  intro x hx
  exact hx.1
