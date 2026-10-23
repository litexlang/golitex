import Mathlib

example : ∀ A B D : Set Real, A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := by intro A B D; ext x; simp [Set.mem_union, Set.mem_inter_iff]; tauto
