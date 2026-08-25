import LitexToMathlibPipelineGenerated

namespace LitexToMathlibPipeline

/-- An ordinary Mathlib consumer imports the generated native theorem and uses
it to construct a downstream set-theoretic fact. -/
theorem closedIntervalNonemptyOfLt
    (a b : ℝ)
    (strict : a < b) :
    (Set.Icc a b).Nonempty := by
  refine ⟨a, le_rfl, ?_⟩
  exact __Compiler_main.Native.litex_real_lt_to_le a b strict

end LitexToMathlibPipeline
