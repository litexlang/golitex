import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
example : ∀ s : Real, (∃ t : Real, t^2 = s) → ∃ u : Real, u^2 = 4*s := by intro s hs; rcases hs with ⟨t, ht⟩; refine ⟨2*t, ?_⟩; nlinarith
