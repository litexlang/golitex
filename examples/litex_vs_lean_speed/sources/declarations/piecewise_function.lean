import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
noncomputable def bench_abs (x : Real) : Real := if 0 ≤ x then x else -x
theorem bench_use : bench_abs (-3) = 3 := by norm_num [bench_abs]
