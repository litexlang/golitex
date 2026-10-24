import Mathlib
set_option Elab.async false

namespace PerturbedGeometric
noncomputable section

def bound (q c d : ℝ) (n : ℕ) : ℝ :=
  q ^ n * c + d * (1 - q ^ n) / (1 - q)

theorem bound_zero {q c d : ℝ} (_hq0 : 0 < q) (_hq1 : q < 1) :
    bound q c d 0 = c := by
  simp [bound]

theorem bound_step {q c d : ℝ} (_hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    bound q c d (n + 1) = q * bound q c d n + d := by
  have hden : 1 - q ≠ 0 := by linarith
  dsimp [bound]
  rw [pow_succ]
  field_simp [hden] <;> ring

theorem affine_recurrence_bound (err : ℕ → ℝ) {q d : ℝ} (n : ℕ)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hrec : ∀ j, err (j + 1) ≤ q * err j + d) :
    err n ≤ bound q (err 0) d n := by
  induction n with
  | zero => simp [bound]
  | succ n ih =>
      calc
        err (n + 1) ≤ q * err n + d := hrec n
        _ ≤ q * bound q (err 0) d n + d :=
          by linarith [mul_le_mul_of_nonneg_left ih (le_of_lt hq0)]
        _ = bound q (err 0) d (n + 1) := (bound_step hq0 hq1 n).symm

theorem noiseless_affine_bound (err : ℕ → ℝ) {q : ℝ} (n : ℕ)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hrec : ∀ j, err (j + 1) ≤ q * err j) :
    err n ≤ q ^ n * err 0 := by
  have h := affine_recurrence_bound err n hq0 hq1 (d := 0)
    (fun j => by simpa using hrec j)
  simpa [bound] using h

#print axioms bound_zero
#print axioms bound_step
#print axioms affine_recurrence_bound
#print axioms noiseless_affine_bound
end
end PerturbedGeometric
