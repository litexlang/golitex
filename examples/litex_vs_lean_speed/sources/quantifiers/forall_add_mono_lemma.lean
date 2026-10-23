import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
example : ∀ a b c : Real, a < b → a+c < b+c := by intro a b c h; simpa only [add_comm] using add_lt_add_right h c
