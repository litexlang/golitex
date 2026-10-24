import Mathlib

theorem type_bridge_square_nonnegative_direct : ∀ n : Nat, (0 : Real) ≤ (n : Real)^2 := fun n => sq_nonneg (n : Real)

#print axioms type_bridge_square_nonnegative_direct
