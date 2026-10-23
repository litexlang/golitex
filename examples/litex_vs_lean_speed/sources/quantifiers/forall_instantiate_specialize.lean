import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
example : ∀ f : Real → Real, (∀ t : Real, 0 < f t) → 0 < f 0 := by intro f hf; exact hf 0
