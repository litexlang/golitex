import Mathlib

example : ∀ f g h : Real → Real, (f ∘ g) ∘ h = f ∘ (g ∘ h) := fun _ _ _ => rfl
