theorem carrier_q_pos_in_q
    (x : ℚ)
    (_hx : x ∈ {q : ℚ | 0 < q}) : x ∈ (Set.univ : Set ℚ) := by
  exact Set.mem_univ x
