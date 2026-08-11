theorem set_union_membership_right
    {α : Type*}
    (A B : Set α)
    (x : α)
    (_hA : True)
    (_hB : True)
    (hxB : x ∈ B) : x ∈ A ∪ B := by
  exact Set.mem_union_right A hxB
