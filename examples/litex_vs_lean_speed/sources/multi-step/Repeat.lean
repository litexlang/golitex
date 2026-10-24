import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

open Lean Elab Command in
elab "#probe " label:str cmd:command : command => do
  let before ← get
  let start ← IO.monoNanosNow
  let mut success := true
  try
    elabCommand cmd
    if (← get).messages.hasErrors then
      success := false
  catch ex =>
    success := false
    IO.println s!"EXCEPTION,{label.getString},{← ex.toMessageData.toString}"
  let elapsed := (← IO.monoNanosNow) - start
  IO.println s!"PROBE,{label.getString},{success},{elapsed}"
  set before

#probe "sum_sq_zero__nlinarith__first" theorem initial_sum_sq_zero_nlinarith : ∀ x y : Real, x^2 + y^2 = 0 → x = 0 ∧ y = 0 := by
  intro x y h
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]

#probe "sum_sq_zero__nlinarith" theorem sample_sum_sq_zero_nlinarith_0 : ∀ x y : Real, x^2 + y^2 = 0 → x = 0 ∧ y = 0 := by
  intro x y h
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]

#probe "sum_sq_zero__nlinarith" theorem sample_sum_sq_zero_nlinarith_1 : ∀ x y : Real, x^2 + y^2 = 0 → x = 0 ∧ y = 0 := by
  intro x y h
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]

#probe "sum_sq_zero__nlinarith" theorem sample_sum_sq_zero_nlinarith_2 : ∀ x y : Real, x^2 + y^2 = 0 → x = 0 ∧ y = 0 := by
  intro x y h
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]

#probe "sum_sq_zero__nlinarith" theorem sample_sum_sq_zero_nlinarith_3 : ∀ x y : Real, x^2 + y^2 = 0 → x = 0 ∧ y = 0 := by
  intro x y h
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]

#probe "sum_sq_zero__nlinarith" theorem sample_sum_sq_zero_nlinarith_4 : ∀ x y : Real, x^2 + y^2 = 0 → x = 0 ∧ y = 0 := by
  intro x y h
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]

#probe "sum_sq_zero__nlinarith" theorem sample_sum_sq_zero_nlinarith_5 : ∀ x y : Real, x^2 + y^2 = 0 → x = 0 ∧ y = 0 := by
  intro x y h
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]

#probe "sum_sq_zero__nlinarith" theorem sample_sum_sq_zero_nlinarith_6 : ∀ x y : Real, x^2 + y^2 = 0 → x = 0 ∧ y = 0 := by
  intro x y h
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]

#probe "positive_ratio__div_pos__first" theorem initial_positive_ratio_div_pos : ∀ x : Real, 0 < x → 0 < x/(x+1) := by
  intro x hx
  have h1 : (0 : Real) < x + 1 := by linarith
  exact div_pos hx h1

#probe "positive_ratio__div_pos" theorem sample_positive_ratio_div_pos_0 : ∀ x : Real, 0 < x → 0 < x/(x+1) := by
  intro x hx
  have h1 : (0 : Real) < x + 1 := by linarith
  exact div_pos hx h1

#probe "positive_ratio__div_pos" theorem sample_positive_ratio_div_pos_1 : ∀ x : Real, 0 < x → 0 < x/(x+1) := by
  intro x hx
  have h1 : (0 : Real) < x + 1 := by linarith
  exact div_pos hx h1

#probe "positive_ratio__div_pos" theorem sample_positive_ratio_div_pos_2 : ∀ x : Real, 0 < x → 0 < x/(x+1) := by
  intro x hx
  have h1 : (0 : Real) < x + 1 := by linarith
  exact div_pos hx h1

#probe "positive_ratio__div_pos" theorem sample_positive_ratio_div_pos_3 : ∀ x : Real, 0 < x → 0 < x/(x+1) := by
  intro x hx
  have h1 : (0 : Real) < x + 1 := by linarith
  exact div_pos hx h1

#probe "positive_ratio__div_pos" theorem sample_positive_ratio_div_pos_4 : ∀ x : Real, 0 < x → 0 < x/(x+1) := by
  intro x hx
  have h1 : (0 : Real) < x + 1 := by linarith
  exact div_pos hx h1

#probe "positive_ratio__div_pos" theorem sample_positive_ratio_div_pos_5 : ∀ x : Real, 0 < x → 0 < x/(x+1) := by
  intro x hx
  have h1 : (0 : Real) < x + 1 := by linarith
  exact div_pos hx h1

#probe "positive_ratio__div_pos" theorem sample_positive_ratio_div_pos_6 : ∀ x : Real, 0 < x → 0 < x/(x+1) := by
  intro x hx
  have h1 : (0 : Real) < x + 1 := by linarith
  exact div_pos hx h1

#probe "mul_cancel__linarith__first" theorem initial_mul_cancel_linarith : ∀ x y : Real, 2*x = 2*y → x = y := by intro x y h; linarith

#probe "mul_cancel__cancel__first" theorem initial_mul_cancel_cancel : ∀ x y : Real, 2*x = 2*y → x = y := by intro x y h; exact mul_left_cancel₀ (by norm_num : (2:Real) ≠ 0) h

#probe "mul_cancel__linarith" theorem sample_mul_cancel_linarith_0 : ∀ x y : Real, 2*x = 2*y → x = y := by intro x y h; linarith

#probe "mul_cancel__linarith" theorem sample_mul_cancel_linarith_1 : ∀ x y : Real, 2*x = 2*y → x = y := by intro x y h; linarith

#probe "mul_cancel__linarith" theorem sample_mul_cancel_linarith_2 : ∀ x y : Real, 2*x = 2*y → x = y := by intro x y h; linarith

#probe "mul_cancel__linarith" theorem sample_mul_cancel_linarith_3 : ∀ x y : Real, 2*x = 2*y → x = y := by intro x y h; linarith

#probe "mul_cancel__linarith" theorem sample_mul_cancel_linarith_4 : ∀ x y : Real, 2*x = 2*y → x = y := by intro x y h; linarith

#probe "mul_cancel__linarith" theorem sample_mul_cancel_linarith_5 : ∀ x y : Real, 2*x = 2*y → x = y := by intro x y h; linarith

#probe "mul_cancel__linarith" theorem sample_mul_cancel_linarith_6 : ∀ x y : Real, 2*x = 2*y → x = y := by intro x y h; linarith

#probe "mul_cancel__cancel" theorem sample_mul_cancel_cancel_0 : ∀ x y : Real, 2*x = 2*y → x = y := by intro x y h; exact mul_left_cancel₀ (by norm_num : (2:Real) ≠ 0) h

#probe "mul_cancel__cancel" theorem sample_mul_cancel_cancel_1 : ∀ x y : Real, 2*x = 2*y → x = y := by intro x y h; exact mul_left_cancel₀ (by norm_num : (2:Real) ≠ 0) h

#probe "mul_cancel__cancel" theorem sample_mul_cancel_cancel_2 : ∀ x y : Real, 2*x = 2*y → x = y := by intro x y h; exact mul_left_cancel₀ (by norm_num : (2:Real) ≠ 0) h

#probe "mul_cancel__cancel" theorem sample_mul_cancel_cancel_3 : ∀ x y : Real, 2*x = 2*y → x = y := by intro x y h; exact mul_left_cancel₀ (by norm_num : (2:Real) ≠ 0) h

#probe "mul_cancel__cancel" theorem sample_mul_cancel_cancel_4 : ∀ x y : Real, 2*x = 2*y → x = y := by intro x y h; exact mul_left_cancel₀ (by norm_num : (2:Real) ≠ 0) h

#probe "mul_cancel__cancel" theorem sample_mul_cancel_cancel_5 : ∀ x y : Real, 2*x = 2*y → x = y := by intro x y h; exact mul_left_cancel₀ (by norm_num : (2:Real) ≠ 0) h

#probe "mul_cancel__cancel" theorem sample_mul_cancel_cancel_6 : ∀ x y : Real, 2*x = 2*y → x = y := by intro x y h; exact mul_left_cancel₀ (by norm_num : (2:Real) ≠ 0) h

#probe "sq_plus_one_pos__positivity__first" theorem initial_sq_plus_one_pos_positivity : ∀ x : Real, 0 < x^2 + 1 := by intro x; positivity

#probe "sq_plus_one_pos__nlinarith__first" theorem initial_sq_plus_one_pos_nlinarith : ∀ x : Real, 0 < x^2 + 1 := by intro x; nlinarith [sq_nonneg x]

#probe "sq_plus_one_pos__positivity" theorem sample_sq_plus_one_pos_positivity_0 : ∀ x : Real, 0 < x^2 + 1 := by intro x; positivity

#probe "sq_plus_one_pos__positivity" theorem sample_sq_plus_one_pos_positivity_1 : ∀ x : Real, 0 < x^2 + 1 := by intro x; positivity

#probe "sq_plus_one_pos__positivity" theorem sample_sq_plus_one_pos_positivity_2 : ∀ x : Real, 0 < x^2 + 1 := by intro x; positivity

#probe "sq_plus_one_pos__positivity" theorem sample_sq_plus_one_pos_positivity_3 : ∀ x : Real, 0 < x^2 + 1 := by intro x; positivity

#probe "sq_plus_one_pos__positivity" theorem sample_sq_plus_one_pos_positivity_4 : ∀ x : Real, 0 < x^2 + 1 := by intro x; positivity

#probe "sq_plus_one_pos__positivity" theorem sample_sq_plus_one_pos_positivity_5 : ∀ x : Real, 0 < x^2 + 1 := by intro x; positivity

#probe "sq_plus_one_pos__positivity" theorem sample_sq_plus_one_pos_positivity_6 : ∀ x : Real, 0 < x^2 + 1 := by intro x; positivity

#probe "sq_plus_one_pos__nlinarith" theorem sample_sq_plus_one_pos_nlinarith_0 : ∀ x : Real, 0 < x^2 + 1 := by intro x; nlinarith [sq_nonneg x]

#probe "sq_plus_one_pos__nlinarith" theorem sample_sq_plus_one_pos_nlinarith_1 : ∀ x : Real, 0 < x^2 + 1 := by intro x; nlinarith [sq_nonneg x]

#probe "sq_plus_one_pos__nlinarith" theorem sample_sq_plus_one_pos_nlinarith_2 : ∀ x : Real, 0 < x^2 + 1 := by intro x; nlinarith [sq_nonneg x]

#probe "sq_plus_one_pos__nlinarith" theorem sample_sq_plus_one_pos_nlinarith_3 : ∀ x : Real, 0 < x^2 + 1 := by intro x; nlinarith [sq_nonneg x]

#probe "sq_plus_one_pos__nlinarith" theorem sample_sq_plus_one_pos_nlinarith_4 : ∀ x : Real, 0 < x^2 + 1 := by intro x; nlinarith [sq_nonneg x]

#probe "sq_plus_one_pos__nlinarith" theorem sample_sq_plus_one_pos_nlinarith_5 : ∀ x : Real, 0 < x^2 + 1 := by intro x; nlinarith [sq_nonneg x]

#probe "sq_plus_one_pos__nlinarith" theorem sample_sq_plus_one_pos_nlinarith_6 : ∀ x : Real, 0 < x^2 + 1 := by intro x; nlinarith [sq_nonneg x]

#probe "sum_sq_ge_two_mul__nlinarith__first" theorem initial_sum_sq_ge_two_mul_nlinarith : ∀ x y : Real, 2*x*y ≤ x^2 + y^2 := by intro x y; nlinarith [sq_nonneg (x-y)]

#probe "sum_sq_ge_two_mul__nlinarith" theorem sample_sum_sq_ge_two_mul_nlinarith_0 : ∀ x y : Real, 2*x*y ≤ x^2 + y^2 := by intro x y; nlinarith [sq_nonneg (x-y)]

#probe "sum_sq_ge_two_mul__nlinarith" theorem sample_sum_sq_ge_two_mul_nlinarith_1 : ∀ x y : Real, 2*x*y ≤ x^2 + y^2 := by intro x y; nlinarith [sq_nonneg (x-y)]

#probe "sum_sq_ge_two_mul__nlinarith" theorem sample_sum_sq_ge_two_mul_nlinarith_2 : ∀ x y : Real, 2*x*y ≤ x^2 + y^2 := by intro x y; nlinarith [sq_nonneg (x-y)]

#probe "sum_sq_ge_two_mul__nlinarith" theorem sample_sum_sq_ge_two_mul_nlinarith_3 : ∀ x y : Real, 2*x*y ≤ x^2 + y^2 := by intro x y; nlinarith [sq_nonneg (x-y)]

#probe "sum_sq_ge_two_mul__nlinarith" theorem sample_sum_sq_ge_two_mul_nlinarith_4 : ∀ x y : Real, 2*x*y ≤ x^2 + y^2 := by intro x y; nlinarith [sq_nonneg (x-y)]

#probe "sum_sq_ge_two_mul__nlinarith" theorem sample_sum_sq_ge_two_mul_nlinarith_5 : ∀ x y : Real, 2*x*y ≤ x^2 + y^2 := by intro x y; nlinarith [sq_nonneg (x-y)]

#probe "sum_sq_ge_two_mul__nlinarith" theorem sample_sum_sq_ge_two_mul_nlinarith_6 : ∀ x y : Real, 2*x*y ≤ x^2 + y^2 := by intro x y; nlinarith [sq_nonneg (x-y)]

#probe "even_witness_above__witness__first" theorem initial_even_witness_above_witness : ∀ n : Nat, 0 < n → ∃ m : Nat, 0 < m ∧ m > n ∧ 2 ∣ m := by
  intro n hn
  exact ⟨2*n, by omega, by omega, ⟨n, by ring⟩⟩

#probe "even_witness_above__witness" theorem sample_even_witness_above_witness_0 : ∀ n : Nat, 0 < n → ∃ m : Nat, 0 < m ∧ m > n ∧ 2 ∣ m := by
  intro n hn
  exact ⟨2*n, by omega, by omega, ⟨n, by ring⟩⟩

#probe "even_witness_above__witness" theorem sample_even_witness_above_witness_1 : ∀ n : Nat, 0 < n → ∃ m : Nat, 0 < m ∧ m > n ∧ 2 ∣ m := by
  intro n hn
  exact ⟨2*n, by omega, by omega, ⟨n, by ring⟩⟩

#probe "even_witness_above__witness" theorem sample_even_witness_above_witness_2 : ∀ n : Nat, 0 < n → ∃ m : Nat, 0 < m ∧ m > n ∧ 2 ∣ m := by
  intro n hn
  exact ⟨2*n, by omega, by omega, ⟨n, by ring⟩⟩

#probe "even_witness_above__witness" theorem sample_even_witness_above_witness_3 : ∀ n : Nat, 0 < n → ∃ m : Nat, 0 < m ∧ m > n ∧ 2 ∣ m := by
  intro n hn
  exact ⟨2*n, by omega, by omega, ⟨n, by ring⟩⟩

#probe "even_witness_above__witness" theorem sample_even_witness_above_witness_4 : ∀ n : Nat, 0 < n → ∃ m : Nat, 0 < m ∧ m > n ∧ 2 ∣ m := by
  intro n hn
  exact ⟨2*n, by omega, by omega, ⟨n, by ring⟩⟩

#probe "even_witness_above__witness" theorem sample_even_witness_above_witness_5 : ∀ n : Nat, 0 < n → ∃ m : Nat, 0 < m ∧ m > n ∧ 2 ∣ m := by
  intro n hn
  exact ⟨2*n, by omega, by omega, ⟨n, by ring⟩⟩

#probe "even_witness_above__witness" theorem sample_even_witness_above_witness_6 : ∀ n : Nat, 0 < n → ∃ m : Nat, 0 < m ∧ m > n ∧ 2 ∣ m := by
  intro n hn
  exact ⟨2*n, by omega, by omega, ⟨n, by ring⟩⟩

#probe "nat_succ_lt_two_mul__omega__first" theorem initial_nat_succ_lt_two_mul_omega : ∀ n : Nat, 0 < n → n < 2*n := by intro n hn; omega

#probe "nat_succ_lt_two_mul__nlinarith__first" theorem initial_nat_succ_lt_two_mul_nlinarith : ∀ n : Nat, 0 < n → n < 2*n := by intro n hn; nlinarith

#probe "nat_succ_lt_two_mul__omega" theorem sample_nat_succ_lt_two_mul_omega_0 : ∀ n : Nat, 0 < n → n < 2*n := by intro n hn; omega

#probe "nat_succ_lt_two_mul__omega" theorem sample_nat_succ_lt_two_mul_omega_1 : ∀ n : Nat, 0 < n → n < 2*n := by intro n hn; omega

#probe "nat_succ_lt_two_mul__omega" theorem sample_nat_succ_lt_two_mul_omega_2 : ∀ n : Nat, 0 < n → n < 2*n := by intro n hn; omega

#probe "nat_succ_lt_two_mul__omega" theorem sample_nat_succ_lt_two_mul_omega_3 : ∀ n : Nat, 0 < n → n < 2*n := by intro n hn; omega

#probe "nat_succ_lt_two_mul__omega" theorem sample_nat_succ_lt_two_mul_omega_4 : ∀ n : Nat, 0 < n → n < 2*n := by intro n hn; omega

#probe "nat_succ_lt_two_mul__omega" theorem sample_nat_succ_lt_two_mul_omega_5 : ∀ n : Nat, 0 < n → n < 2*n := by intro n hn; omega

#probe "nat_succ_lt_two_mul__omega" theorem sample_nat_succ_lt_two_mul_omega_6 : ∀ n : Nat, 0 < n → n < 2*n := by intro n hn; omega

#probe "nat_succ_lt_two_mul__nlinarith" theorem sample_nat_succ_lt_two_mul_nlinarith_0 : ∀ n : Nat, 0 < n → n < 2*n := by intro n hn; nlinarith

#probe "nat_succ_lt_two_mul__nlinarith" theorem sample_nat_succ_lt_two_mul_nlinarith_1 : ∀ n : Nat, 0 < n → n < 2*n := by intro n hn; nlinarith

#probe "nat_succ_lt_two_mul__nlinarith" theorem sample_nat_succ_lt_two_mul_nlinarith_2 : ∀ n : Nat, 0 < n → n < 2*n := by intro n hn; nlinarith

#probe "nat_succ_lt_two_mul__nlinarith" theorem sample_nat_succ_lt_two_mul_nlinarith_3 : ∀ n : Nat, 0 < n → n < 2*n := by intro n hn; nlinarith

#probe "nat_succ_lt_two_mul__nlinarith" theorem sample_nat_succ_lt_two_mul_nlinarith_4 : ∀ n : Nat, 0 < n → n < 2*n := by intro n hn; nlinarith

#probe "nat_succ_lt_two_mul__nlinarith" theorem sample_nat_succ_lt_two_mul_nlinarith_5 : ∀ n : Nat, 0 < n → n < 2*n := by intro n hn; nlinarith

#probe "nat_succ_lt_two_mul__nlinarith" theorem sample_nat_succ_lt_two_mul_nlinarith_6 : ∀ n : Nat, 0 < n → n < 2*n := by intro n hn; nlinarith
