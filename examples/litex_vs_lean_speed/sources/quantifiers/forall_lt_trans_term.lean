import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
example : ∀ a b c : Real, a < b → b < c → a < c := fun a b c hab hbc => lt_trans hab hbc
