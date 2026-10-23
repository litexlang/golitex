import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
example : ∀ a b : Real, a < b → ∃ m : Real, a < m ∧ m < b := fun a b h => exists_between h
