import Mathlib

example : ∀ p : Real × Real, (p.1, p.2) = p := fun p => Prod.mk.eta (p := p)
