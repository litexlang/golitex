theorem set_set_minus_membership
    {α : Type*}
    (A B : Set α)
    (x : α)
    (_hA : True)
    (_hB : True)
    (hxA : x ∈ A)
    (hxB : x ∉ B) : x ∈ A \ B := by
  exact ⟨hxA, hxB⟩
