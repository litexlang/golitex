import Mathlib

example : ∀ (a : Int) (c : Int), c ≠ 0 → c ∣ a * c := fun a c _ => dvd_mul_left c a
