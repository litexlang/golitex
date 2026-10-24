import Mathlib

theorem type_bridge_cast_order_direct : ∀ m n : Nat, m < n → (m : Real) < (n : Real) := fun _ _ h => Nat.cast_lt.mpr h

#print axioms type_bridge_cast_order_direct
