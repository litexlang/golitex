import Mathlib

example : ∀ A B D : Set Real, A ⊆ B → A ∩ D ⊆ B ∩ D := fun A B D h => Set.inter_subset_inter_left D h
