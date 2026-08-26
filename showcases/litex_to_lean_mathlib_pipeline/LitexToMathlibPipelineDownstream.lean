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

/-- The downstream client can retain the property certificate, rather than
immediately flattening it back to a bare equality. -/
theorem firstHundredPositiveOddIntegersAreSquareOfHundred :
    ExternalAI.IsSquareOf
      (∑ k ∈ Finset.Icc (1 : ℤ) 100, (2 * k - 1)) 100 :=
  ExternalAI.sum_first_odds_is_square_of_n 100 (by norm_num)

/-- A new conclusion obtained by consuming the reusable property law. -/
theorem firstHundredPositiveOddIntegersSumNonnegative :
    0 ≤ ∑ k ∈ Finset.Icc (1 : ℤ) 100, (2 * k - 1) :=
  ExternalAI.sum_first_odds_nonnegative 100 (by norm_num)

end LitexToMathlibPipeline
