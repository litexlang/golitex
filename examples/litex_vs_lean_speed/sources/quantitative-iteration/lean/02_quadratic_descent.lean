import Mathlib
set_option Elab.async false

namespace QuadraticDescent
noncomputable section

def energy (a b x : ℝ) : ℝ := a * (x - b) ^ 2 / 2
def gradientStep (a b eta x : ℝ) : ℝ := x - eta * a * (x - b)

theorem gradient_error_identity {a b eta x : ℝ} (_ha : 0 < a) :
    gradientStep a b eta x - b = (1 - eta * a) * (x - b) := by
  dsimp [gradientStep]
  ring

theorem gradient_drop_identity {a b eta x : ℝ} (ha : 0 < a) :
    energy a b x - energy a b (gradientStep a b eta x) =
      eta * a ^ 2 * (2 - eta * a) * (x - b) ^ 2 / 2 := by
  unfold energy
  rw [gradient_error_identity ha]
  ring

theorem gradient_descent {a b eta x : ℝ} (ha : 0 < a)
    (heta : 0 < eta) (hstep : eta * a < 2) :
    energy a b (gradientStep a b eta x) ≤ energy a b x := by
  have hpos : 0 < 2 - eta * a := by linarith
  have hdrop : 0 ≤ eta * a ^ 2 * (2 - eta * a) * (x - b) ^ 2 / 2 := by
    positivity
  have hid := gradient_drop_identity (b := b) (eta := eta) (x := x) ha
  linarith

theorem gradient_strict_descent {a b eta x : ℝ} (ha : 0 < a)
    (heta : 0 < eta) (hstep : eta * a < 2) (hxb : x ≠ b) :
    energy a b (gradientStep a b eta x) < energy a b x := by
  have hpos : 0 < 2 - eta * a := by linarith
  have hne : x - b ≠ 0 := sub_ne_zero.mpr hxb
  have hdrop : 0 < eta * a ^ 2 * (2 - eta * a) * (x - b) ^ 2 / 2 := by
    positivity
  have hid := gradient_drop_identity (b := b) (eta := eta) (x := x) ha
  linarith

example : energy 2 3 (gradientStep 2 3 (1 / 4) 5) < energy 2 3 5 :=
  gradient_strict_descent (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms gradient_error_identity
#print axioms gradient_drop_identity
#print axioms gradient_descent
#print axioms gradient_strict_descent
end
end QuadraticDescent
