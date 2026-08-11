theorem set_subset_eq_set_minus_recovery
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True)
    (h : B ⊆ A) : B = A \ (A \ B) := by
  classical
  ext x
  constructor
  · intro hxB
    exact ⟨h hxB, fun hxAB => hxAB.2 hxB⟩
  · intro hx
    by_contra hxB
    exact hx.2 ⟨hx.1, hxB⟩
