import Mathlib

example : ∀ A B : Set Real, A ⊆ B → A ∪ B = B := fun A B h => Set.union_eq_right.mpr h
