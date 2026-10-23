import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def bench_fac : Nat → Nat
  | 0 => 1
  | n+1 => (n+1)*bench_fac n
theorem bench_use : bench_fac 5 = 120 := by rfl
