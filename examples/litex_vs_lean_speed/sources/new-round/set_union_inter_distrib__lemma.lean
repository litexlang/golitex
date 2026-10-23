import Mathlib

example : ∀ A B D : Set Real, A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := fun A B D => Set.union_inter_distrib_left A B D
