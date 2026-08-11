theorem set_intersect_finite
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True)
    (hA : A.Finite)
    (_hBFinite : B.Finite) : (A ∩ B).Finite := by
  apply hA.subset
  intro x hx
  exact hx.1
