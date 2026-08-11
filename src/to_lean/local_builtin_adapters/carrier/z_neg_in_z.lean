theorem carrier_z_neg_in_z
    (x : ℤ)
    (_hx : x ∈ {z : ℤ | z < 0}) : x ∈ (Set.univ : Set ℤ) := by
  exact Set.mem_univ x
