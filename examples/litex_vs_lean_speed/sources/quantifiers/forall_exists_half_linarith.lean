import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
example : ∀ ε : Real, 0 < ε → ∃ δ : Real, 0 < δ ∧ δ < ε := by intro ε h; refine ⟨ε/2, ?_, ?_⟩ <;> linarith
