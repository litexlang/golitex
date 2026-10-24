import Mathlib

example : ∀ ε : Real, 0 < ε → ∃ n : Nat, 0 < n ∧ 1/(n:Real) < ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n+1, by omega, ?_⟩
  simpa using hn
