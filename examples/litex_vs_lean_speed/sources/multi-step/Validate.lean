import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

theorem validated_sum_sq_zero_nlinarith : ∀ x y : Real, x^2 + y^2 = 0 → x = 0 ∧ y = 0 := by
  intro x y h
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]

theorem validated_positive_ratio_div_pos : ∀ x : Real, 0 < x → 0 < x/(x+1) := by
  intro x hx
  have h1 : (0 : Real) < x + 1 := by linarith
  exact div_pos hx h1

theorem validated_mul_cancel_linarith : ∀ x y : Real, 2*x = 2*y → x = y := by intro x y h; linarith

theorem validated_mul_cancel_cancel : ∀ x y : Real, 2*x = 2*y → x = y := by intro x y h; exact mul_left_cancel₀ (by norm_num : (2:Real) ≠ 0) h

theorem validated_sq_plus_one_pos_positivity : ∀ x : Real, 0 < x^2 + 1 := by intro x; positivity

theorem validated_sq_plus_one_pos_nlinarith : ∀ x : Real, 0 < x^2 + 1 := by intro x; nlinarith [sq_nonneg x]

theorem validated_sum_sq_ge_two_mul_nlinarith : ∀ x y : Real, 2*x*y ≤ x^2 + y^2 := by intro x y; nlinarith [sq_nonneg (x-y)]

theorem validated_even_witness_above_witness : ∀ n : Nat, 0 < n → ∃ m : Nat, 0 < m ∧ m > n ∧ 2 ∣ m := by
  intro n hn
  exact ⟨2*n, by omega, by omega, ⟨n, by ring⟩⟩

theorem validated_nat_succ_lt_two_mul_omega : ∀ n : Nat, 0 < n → n < 2*n := by intro n hn; omega

theorem validated_nat_succ_lt_two_mul_nlinarith : ∀ n : Nat, 0 < n → n < 2*n := by intro n hn; nlinarith

#print axioms validated_sum_sq_zero_nlinarith

#print axioms validated_positive_ratio_div_pos

#print axioms validated_mul_cancel_linarith

#print axioms validated_mul_cancel_cancel

#print axioms validated_sq_plus_one_pos_positivity

#print axioms validated_sq_plus_one_pos_nlinarith

#print axioms validated_sum_sq_ge_two_mul_nlinarith

#print axioms validated_even_witness_above_witness

#print axioms validated_nat_succ_lt_two_mul_omega

#print axioms validated_nat_succ_lt_two_mul_nlinarith
