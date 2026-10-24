import Mathlib

theorem type_bridge_cast_addition_automation : ∀ m n : Nat, ((m + n : Nat) : Real) = (m : Real) + (n : Real) := by
  intro m n
  norm_cast

#print axioms type_bridge_cast_addition_automation
