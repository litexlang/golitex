import Mathlib

theorem type_bridge_square_nonnegative_bridge : ∀ n : Nat, (0 : Real) ≤ (n : Real)^2 := by
  intro n
  have h : 0 ≤ n^2 := Nat.zero_le _
  exact_mod_cast h

#print axioms type_bridge_square_nonnegative_bridge
