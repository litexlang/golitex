import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def bench_square (x : Real) : Real := x^2
theorem bench_use : bench_square 3 = 9 := by norm_num [bench_square]
