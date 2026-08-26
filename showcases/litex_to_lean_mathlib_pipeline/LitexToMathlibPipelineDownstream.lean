import LitexToMathlibPipelineAdapter

namespace LitexToMathlibPipeline

/-- An ordinary Mathlib consumer imports the external adapter, then specializes
its native theorem to a concrete calculation. -/
theorem firstHundredPositiveOddIntegersSum :
    ∑ k ∈ Finset.Icc (1 : ℤ) 100, (2 * k - 1) = 10000 := by
  calc
    ∑ k ∈ Finset.Icc (1 : ℤ) 100, (2 * k - 1) = (100 : ℤ) ^ 2 :=
      ExternalAI.sum_first_odds 100 (by norm_num)
    _ = 10000 := by norm_num

end LitexToMathlibPipeline
