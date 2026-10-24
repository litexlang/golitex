import Mathlib
set_option Elab.async false

namespace ParametricNewton
noncomputable section

def newton (a x : ℝ) : ℝ := (x + a / x) / 2

theorem newton_positive {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    0 < newton a x := by
  unfold newton
  positivity

theorem newton_residual_identity {a x : ℝ} (_ha : 0 < a) (hx : 0 < x) :
    4 * x ^ 2 * (newton a x ^ 2 - a) = (x ^ 2 - a) ^ 2 := by
  unfold newton
  field_simp [ne_of_gt hx] <;> ring

theorem newton_above_root {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    a ≤ newton a x ^ 2 := by
  have hp : 0 < 4 * x ^ 2 := by positivity
  have hid : newton a x ^ 2 - a = (x ^ 2 - a) ^ 2 / (4 * x ^ 2) := by
    apply (eq_div_iff (ne_of_gt hp)).2
    calc
      (newton a x ^ 2 - a) * (4 * x ^ 2) =
          4 * x ^ 2 * (newton a x ^ 2 - a) := by ring
      _ = (x ^ 2 - a) ^ 2 := newton_residual_identity ha hx
  have hnonneg : 0 ≤ newton a x ^ 2 - a := by
    rw [hid]
    positivity
  linarith

example : newton 9 4 = 25 / 8 := by norm_num [newton]
example : (9 : ℝ) ≤ newton 9 4 ^ 2 :=
  newton_above_root (by norm_num) (by norm_num)

#print axioms newton_positive
#print axioms newton_residual_identity
#print axioms newton_above_root
end
end ParametricNewton
