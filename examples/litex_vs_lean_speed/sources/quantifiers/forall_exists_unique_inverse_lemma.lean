import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
example : ∀ a : Real, ∃! x : Real, x+a = 0 := by intro a; refine ⟨-a, neg_add_cancel a, ?_⟩; intro y hy; exact eq_neg_of_add_eq_zero_left hy
