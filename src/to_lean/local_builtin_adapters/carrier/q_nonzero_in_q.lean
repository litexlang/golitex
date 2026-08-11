theorem carrier_q_nonzero_in_q
    (x : ℚ)
    (_hx : x ∈ {q : ℚ | q ≠ 0}) : x ∈ (Set.univ : Set ℚ) := by
  exact Set.mem_univ x
