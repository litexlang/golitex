import Mathlib

example : ∀ n : Nat, 0 < n → n < 2*n := by intro n hn; omega
