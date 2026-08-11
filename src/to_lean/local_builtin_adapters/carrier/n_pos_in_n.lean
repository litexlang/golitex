theorem carrier_n_pos_in_n
    (x : ℕ)
    (_hx : x ∈ {n : ℕ | 0 < n}) : x ∈ (Set.univ : Set ℕ) := by
  exact Set.mem_univ x
