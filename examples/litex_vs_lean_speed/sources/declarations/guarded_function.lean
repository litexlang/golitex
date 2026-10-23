import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
noncomputable def bench_recip (x : Real) (_hx : x ≠ 0) : Real := 1/x
theorem bench_use : bench_recip 2 (by norm_num) = 1/2 := by rfl
