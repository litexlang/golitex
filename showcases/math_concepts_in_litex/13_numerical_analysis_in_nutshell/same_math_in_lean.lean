import Mathlib

/- The same real Newton iteration, residual gap, and gap bound as the Litex
showcase. The supporting lemmas and induction are proved here; none is a
setting field. -/

namespace NumericalAnalysisSameMathInLean

noncomputable section

def sqrtTwoResidual (x : ℝ) : ℝ := x ^ 2 - 2

def newtonSqrtTwo (x : ℝ) : ℝ := (x + 2 / x) / 2

def sqrtTwoNewtonIterate : ℕ → ℝ
  | 0 => 1
  | n + 1 => newtonSqrtTwo (sqrtTwoNewtonIterate n)

def sqrtTwoNewtonGap (n : ℕ) : ℝ :=
  |sqrtTwoResidual (sqrtTwoNewtonIterate n)|

def sqrtTwoNewtonGapBound (n : ℕ) : ℝ :=
  4 * (1 / 4 : ℝ) ^ (2 ^ n)

theorem newtonSqrtTwoResidualIdentity {x : ℝ} (hx : x ≠ 0) :
    4 * x ^ 2 * sqrtTwoResidual (newtonSqrtTwo x) =
      sqrtTwoResidual x ^ 2 := by
  unfold sqrtTwoResidual newtonSqrtTwo
  field_simp [hx]
  ring

theorem newtonSqrtTwoGreaterThanOne {x : ℝ} (hx : 0 < x) :
    1 < newtonSqrtTwo x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hformula :
      newtonSqrtTwo x - 1 = ((x - 1) ^ 2 + 1) / (2 * x) := by
    unfold newtonSqrtTwo
    field_simp [hx0]
    ring
  apply sub_pos.mp
  rw [hformula]
  exact div_pos (by nlinarith [sq_nonneg (x - 1)]) (mul_pos (by norm_num) hx)

theorem sqrtTwoNewtonIterateStep (n : ℕ) :
    sqrtTwoNewtonIterate (n + 1) =
      newtonSqrtTwo (sqrtTwoNewtonIterate n) := by
  rfl

theorem sqrtTwoNewtonIterateAtLeastOne (n : ℕ) :
    1 ≤ sqrtTwoNewtonIterate n := by
  induction n with
  | zero => norm_num [sqrtTwoNewtonIterate]
  | succ n ih =>
      rw [sqrtTwoNewtonIterateStep]
      exact le_of_lt (newtonSqrtTwoGreaterThanOne (lt_of_lt_of_le zero_lt_one ih))

theorem newtonSqrtTwoResidualNonnegative {x : ℝ} (hx : 0 < x) :
    0 ≤ sqrtTwoResidual (newtonSqrtTwo x) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hfactor : 0 < 4 * x ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hx)
  have hquotient :
      sqrtTwoResidual (newtonSqrtTwo x) =
        sqrtTwoResidual x ^ 2 / (4 * x ^ 2) := by
    apply (eq_div_iff (ne_of_gt hfactor)).2
    calc
      sqrtTwoResidual (newtonSqrtTwo x) * (4 * x ^ 2) =
          4 * x ^ 2 * sqrtTwoResidual (newtonSqrtTwo x) := by ring
      _ = sqrtTwoResidual x ^ 2 := newtonSqrtTwoResidualIdentity hx0
  rw [hquotient]
  positivity

theorem newtonSqrtTwoOneStepGapIdentity {x : ℝ} (hx : 0 < x) :
    4 * x ^ 2 * |sqrtTwoResidual (newtonSqrtTwo x)| =
      |sqrtTwoResidual x| ^ 2 := by
  rw [abs_of_nonneg (newtonSqrtTwoResidualNonnegative hx), sq_abs]
  exact newtonSqrtTwoResidualIdentity (ne_of_gt hx)

theorem sqrtTwoNewtonGapStepIdentity (n : ℕ) :
    4 * sqrtTwoNewtonIterate n ^ 2 * sqrtTwoNewtonGap (n + 1) =
      sqrtTwoNewtonGap n ^ 2 := by
  have hpositive : 0 < sqrtTwoNewtonIterate n :=
    lt_of_lt_of_le zero_lt_one (sqrtTwoNewtonIterateAtLeastOne n)
  simpa [sqrtTwoNewtonGap, sqrtTwoNewtonIterateStep] using
    newtonSqrtTwoOneStepGapIdentity hpositive

theorem sqrtTwoNewtonGapContractsQuadratically (n : ℕ) :
    sqrtTwoNewtonGap (n + 1) ≤ sqrtTwoNewtonGap n ^ 2 / 4 := by
  let x := sqrtTwoNewtonIterate n
  have hx : 1 ≤ x := sqrtTwoNewtonIterateAtLeastOne n
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hx2 : 1 ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
  have hden : 0 < 4 * x ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hxpos)
  have hstep :
      sqrtTwoNewtonGap (n + 1) =
        sqrtTwoNewtonGap n ^ 2 / (4 * x ^ 2) := by
    apply (eq_div_iff (ne_of_gt hden)).2
    calc
      sqrtTwoNewtonGap (n + 1) * (4 * x ^ 2) =
          4 * x ^ 2 * sqrtTwoNewtonGap (n + 1) := by ring
      _ = sqrtTwoNewtonGap n ^ 2 := by
        simpa [x] using sqrtTwoNewtonGapStepIdentity n
  rw [hstep]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by nlinarith)

theorem sqrtTwoNewtonGapBoundStep (n : ℕ) :
    sqrtTwoNewtonGapBound (n + 1) =
      sqrtTwoNewtonGapBound n ^ 2 / 4 := by
  have hexponent : 2 ^ (n + 1) = 2 ^ n * 2 := by
    rw [pow_succ]
  unfold sqrtTwoNewtonGapBound
  rw [hexponent, pow_mul]
  ring

theorem sqrtTwoNewtonGapLeBound (n : ℕ) :
    sqrtTwoNewtonGap n ≤ sqrtTwoNewtonGapBound n := by
  induction n with
  | zero =>
      norm_num [sqrtTwoNewtonGap, sqrtTwoNewtonGapBound,
        sqrtTwoNewtonIterate, sqrtTwoResidual]
  | succ n ih =>
      have hgap : 0 ≤ sqrtTwoNewtonGap n := abs_nonneg _
      have hbound : 0 ≤ sqrtTwoNewtonGapBound n := by
        unfold sqrtTwoNewtonGapBound
        positivity
      have hsquare :
          sqrtTwoNewtonGap n ^ 2 ≤ sqrtTwoNewtonGapBound n ^ 2 := by
        nlinarith
      calc
        sqrtTwoNewtonGap (n + 1) ≤ sqrtTwoNewtonGap n ^ 2 / 4 :=
          sqrtTwoNewtonGapContractsQuadratically n
        _ ≤ sqrtTwoNewtonGapBound n ^ 2 / 4 := by linarith
        _ = sqrtTwoNewtonGapBound (n + 1) :=
          (sqrtTwoNewtonGapBoundStep n).symm

example : newtonSqrtTwo 1 = 3 / 2 := by norm_num [newtonSqrtTwo]
example : newtonSqrtTwo (3 / 2) = 17 / 12 := by norm_num [newtonSqrtTwo]

example : sqrtTwoNewtonGap 2 ≤ 1 / 64 := by
  calc
    sqrtTwoNewtonGap 2 ≤ sqrtTwoNewtonGapBound 2 :=
      sqrtTwoNewtonGapLeBound 2
    _ = 1 / 64 := by norm_num [sqrtTwoNewtonGapBound]

end

end NumericalAnalysisSameMathInLean
