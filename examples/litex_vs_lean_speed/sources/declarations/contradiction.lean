import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
theorem bench_use : ¬ ∃ x : Real, x^2 = -1 := by
  by_contra h
  obtain ⟨x,hx⟩ := h
  nlinarith [sq_nonneg x]
