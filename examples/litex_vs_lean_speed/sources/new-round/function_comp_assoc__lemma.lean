import Mathlib

example : ∀ f g h : Real → Real, (f ∘ g) ∘ h = f ∘ (g ∘ h) := fun f g h => Function.comp_assoc f g h
