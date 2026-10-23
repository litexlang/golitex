import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
structure BenchPoint where
  x : Real
  y : Real
def bench_point : BenchPoint := ⟨1,2⟩
theorem bench_use : bench_point.x = 1 := by rfl
