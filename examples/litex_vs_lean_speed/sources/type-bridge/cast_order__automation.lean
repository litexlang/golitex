import Mathlib

theorem type_bridge_cast_order_automation : ∀ m n : Nat, m < n → (m : Real) < (n : Real) := by
  intro m n h
  exact_mod_cast h

#print axioms type_bridge_cast_order_automation
