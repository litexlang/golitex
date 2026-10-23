import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
theorem bench_positive_is_nonzero : ∀ x : Real, 0 < x → x ≠ 0 := by
  intro x hx
  exact ne_of_gt hx
theorem bench_use : (3 : Real) ≠ 0 := bench_positive_is_nonzero 3 (by norm_num)
