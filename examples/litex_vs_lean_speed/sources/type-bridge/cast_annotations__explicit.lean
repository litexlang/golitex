import Mathlib

theorem type_bridge_cast_annotations_explicit : ∀ (a : Int) (d : Nat), 0 < d → a = (d : Int) * (a / (d : Int)) + a % (d : Int) := fun a d _ => (Int.mul_ediv_add_emod a (d : Int)).symm

#print axioms type_bridge_cast_annotations_explicit
