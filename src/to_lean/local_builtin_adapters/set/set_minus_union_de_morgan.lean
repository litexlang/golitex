theorem set_set_minus_union_de_morgan
    {α : Type*}
    (A B C : Set α)
    (_hA : True)
    (_hB : True)
    (_hC : True) : A \ (B ∪ C) = (A \ B) ∩ (A \ C) := by
  exact (Set.diff_inter_diff (s := A) (t := B) (u := C)).symm
