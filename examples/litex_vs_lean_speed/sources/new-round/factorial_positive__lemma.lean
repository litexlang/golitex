import Mathlib

example : ∀ n : Nat, 0 < n.factorial := fun n => Nat.factorial_pos n
