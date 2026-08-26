import LitexToMathlibPipelineGenerated

namespace LitexToMathlibPipeline.ExternalAI

/-- A native Mathlib interface authored outside ToLean.  The generated module
is imported for context, but this theorem is deliberately a separate Lean
artifact: the compiler never invents this statement or proof. -/
theorem sum_first_odds (n : ℤ) (one_le_n : (1 : ℤ) ≤ n) :
    ∑ k ∈ Finset.Icc (1 : ℤ) n, (2 * k - 1) = n ^ 2 := by
  exact Int.leInduction
    (motive := fun value : ℤ => fun _ =>
      ∑ k ∈ Finset.Icc (1 : ℤ) value, (2 * k - 1) = value ^ 2)
    (by norm_num)
    (fun value _value_ge_one ih => by
      rw [← Finset.insert_Icc_right_eq_Icc_add_one
        (by omega : (1 : ℤ) ≤ value + 1)]
      rw [Finset.sum_insert (by simp)]
      rw [ih]
      ring)
    n one_le_n

end LitexToMathlibPipeline.ExternalAI
