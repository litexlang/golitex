import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
theorem bench_use : ∀ x : Real, |x| = x ∨ |x| = -x := by
  intro x
  by_cases h : 0 ≤ x
  · exact Or.inl (abs_of_nonneg h)
  · exact Or.inr (abs_of_neg (lt_of_not_ge h))
