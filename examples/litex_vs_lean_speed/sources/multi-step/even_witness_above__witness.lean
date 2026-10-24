import Mathlib

example : ∀ n : Nat, 0 < n → ∃ m : Nat, 0 < m ∧ m > n ∧ 2 ∣ m := by
  intro n hn
  exact ⟨2*n, by omega, by omega, ⟨n, by ring⟩⟩
