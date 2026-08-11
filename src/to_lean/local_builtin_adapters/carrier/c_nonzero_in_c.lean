theorem carrier_c_nonzero_in_c
    (x : ℂ)
    (_hx : x ∈ {c : ℂ | c ≠ 0}) : x ∈ (Set.univ : Set ℂ) := by
  exact Set.mem_univ x
