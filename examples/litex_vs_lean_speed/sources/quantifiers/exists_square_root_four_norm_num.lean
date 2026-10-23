import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
example : ∃ w : Real, w^2 = 4 := by refine ⟨2, ?_⟩; norm_num
