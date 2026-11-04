import Litex.ElementaryFunctions

namespace Litex

/-- A rational multiple of pi is a sine zero only at an integer coefficient. -/
theorem sinRationalPiNonzero (p q : ℤ) (hq : q ≠ 0) (h : ¬ q ∣ p) :
    Real.sin (((p : ℝ) / (q : ℝ)) * Real.pi) ≠ 0 := by
  intro hz
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hz
  have hc : (n : ℝ) = (p : ℝ) / (q : ℝ) :=
    mul_right_cancel₀ (ne_of_gt Real.pi_pos) hn
  have hi : n * q = p := by
    exact_mod_cast (eq_div_iff (by exact_mod_cast hq : (q : ℝ) ≠ 0)).mp hc
  exact h ⟨n, hi.symm.trans (mul_comm n q)⟩

/-- Cosine's half-integer zero condition, without a bounded rational shift. -/
theorem cosRationalPiNonzero (p q : ℤ) (hq : q ≠ 0)
    (h : ¬ (2 * q) ∣ (2 * p + q)) :
    Real.cos (((p : ℝ) / (q : ℝ)) * Real.pi) ≠ 0 := by
  intro hz
  have angle : (p : ℝ) / q * Real.pi + Real.pi / 2 =
      ((p : ℝ) / q + 1 / 2) * Real.pi := by ring
  have hs : Real.sin ((((p : ℝ) / q) + 1 / 2) * Real.pi) = 0 := by
    rw [← angle, Real.sin_add_pi_div_two]
    exact hz
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
  have hc : (n : ℝ) = (p : ℝ) / q + 1 / 2 :=
    mul_right_cancel₀ (ne_of_gt Real.pi_pos) hn
  have shifted : (n : ℝ) - 1 / 2 = (p : ℝ) / q := by linarith [hc]
  have product : ((n : ℝ) - 1 / 2) * q = (p : ℝ) :=
    (eq_div_iff (by exact_mod_cast hq : (q : ℝ) ≠ 0)).mp shifted
  have realEquation : (2 * (q : ℝ)) * n = 2 * (p : ℝ) + q := by
    calc
      (2 * (q : ℝ)) * n = 2 * (((n : ℝ) - 1 / 2) * q) + q := by ring
      _ = 2 * (p : ℝ) + q := by rw [product]
  have integerEquation : (2 * q) * n = 2 * p + q := by exact_mod_cast realEquation
  exact h ⟨n, integerEquation.symm⟩

end Litex
