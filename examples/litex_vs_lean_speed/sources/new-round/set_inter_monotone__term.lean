import Mathlib

example : ∀ A B D : Set Real, A ⊆ B → A ∩ D ⊆ B ∩ D := fun A B D h x hx => ⟨h hx.1, hx.2⟩
