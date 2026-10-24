import Mathlib

example : ∀ A B : Set Real, A ⊆ B → A ∪ B = B := by
  intro A B h
  ext x
  constructor
  · rintro (hx | hx)
    · exact h hx
    · exact hx
  · intro hx; exact Or.inr hx
