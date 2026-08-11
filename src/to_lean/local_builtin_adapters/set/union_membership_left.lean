theorem set_union_membership_left
    {α : Type*}
    (A B : Set α)
    (x : α)
    (_hA : True)
    (_hB : True)
    (hxA : x ∈ A) : x ∈ A ∪ B := by
  exact Set.mem_union_left B hxA
