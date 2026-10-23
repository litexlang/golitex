import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
example : ∀ x y : Real, x ≤ y → y ≤ x → x = y := by intro x y hxy hyx; linarith
