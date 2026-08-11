theorem carrier_r_pos_in_r
    (x : ℝ)
    (_hx : x ∈ {r : ℝ | 0 < r}) : x ∈ (Set.univ : Set ℝ) := by
  exact Set.mem_univ x
