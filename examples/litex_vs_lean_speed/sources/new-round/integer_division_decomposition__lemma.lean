import Mathlib

example : ∀ (a : Int) (d : Nat), 0 < d → a = (d : Int) * (a / (d : Int)) + a % (d : Int) := fun a d _ => (Int.mul_ediv_add_emod a (d : Int)).symm
