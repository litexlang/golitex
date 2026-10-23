import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
example : ∀ a b : Real, ∃ u : Real, a ≤ u ∧ b ≤ u := by intro a b; exact ⟨max a b, le_max_left a b, le_max_right a b⟩
