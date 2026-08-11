theorem carrier_r_neg_in_r
    (x : ℝ)
    (_hx : x ∈ {r : ℝ | r < 0}) : x ∈ (Set.univ : Set ℝ) := by
  exact Set.mem_univ x
