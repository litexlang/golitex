import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
example : ∀ a : Real, ∃! x : Real, x+a = 0 := by
  intro a
  refine ⟨-a, by ring, ?_⟩
  intro y hy
  linarith
