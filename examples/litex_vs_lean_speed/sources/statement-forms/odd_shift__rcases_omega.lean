import Mathlib

example : ∀ n : Int, (∃ t : Int, n = 2*t + 1) → ∃ t : Int, 3*n + 2 = 2*t + 1 := by
  rintro n ⟨k, hk⟩
  exact ⟨3*k + 2, by omega⟩
