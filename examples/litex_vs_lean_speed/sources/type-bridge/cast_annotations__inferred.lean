import Mathlib

theorem type_bridge_cast_annotations_inferred : ∀ (a : Int) (d : Nat), 0 < d → a = (d : Int) * (a / (d : Int)) + a % (d : Int) := fun a d _ => (Int.mul_ediv_add_emod a d).symm

#print axioms type_bridge_cast_annotations_inferred
