import Mathlib

theorem type_bridge_cast_addition_direct : ∀ m n : Nat, ((m + n : Nat) : Real) = (m : Real) + (n : Real) := fun m n => Nat.cast_add m n

#print axioms type_bridge_cast_addition_direct
