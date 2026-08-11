theorem set_set_minus_recover_subset
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True)
    (h : B ⊆ A) : A \ (A \ B) = B := by
  classical
  ext x
  constructor
  · intro hx
    by_contra hxB
    exact hx.2 ⟨hx.1, hxB⟩
  · intro hxB
    exact ⟨h hxB, fun hxAB => hxAB.2 hxB⟩
