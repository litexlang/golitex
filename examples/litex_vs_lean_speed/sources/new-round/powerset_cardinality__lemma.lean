import Mathlib

example : ∀ s : Finset Nat, s.powerset.card = 2 ^ s.card := fun s => Finset.card_powerset s
