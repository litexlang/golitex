import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_integer_x5f_natural_x5f_square_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.Z (M := M))) (h_1 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i1), Litex.In _value_i1 (Litex.N (M := M)) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_16 h_1
    have h_31 : Litex.In _value_i1 (Litex.N (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (1 : ℂ)) _value_i1 h_16 ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
              have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
              have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_1)
          )
      )
    have h_2 : Litex.In _value_i1 (Litex.N (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_31
          )
      )
    have h_54 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.naturalNonnegative _value_i1 h_2)
          )
      )
    exact h_2
  )

noncomputable def _object_i2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.natural (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (1 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r ≤ _s)) (fun (_raw_i3 : M.Value) => (M.powValue _raw_i3 (M.number (2 : ℂ)))) (by
  intro _raw_i3 h_116 h_55
  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_116)
  have h_116 : Litex.In _value_i3 (Litex.Z (M := M)) := h_116
  have h_55 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_r _s : ℝ), (M.number (1 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r ≤ _s)
            exact h_55)
        )
    )
  have h_131 : Litex.In _value_i3 (Litex.N (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (1 : ℂ)) _value_i3 h_116 ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_55)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.integerToReal _value_i3 h_116) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
    exact Litex.In _atomic_wd_1_0 (Litex.N (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.integerToReal _value_i3 h_116) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
    exact (by
      let _litex_power := _atomic_wd_1_0
      have _elaborated_power_base := h_131
      have _elaborated_power_exponent := (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
      have _recorded_power_base : Litex.In _litex_power.val.base (Litex.N (M := M)) := _elaborated_power_base
      have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.N (M := M)) := _elaborated_power_exponent
      exact Litex.powStructuralInN _litex_power _recorded_power_base _recorded_power_exponent
    ))))
theorem h_242 : Litex.In (_object_i2 (M := M)) (Litex.fnSet ((_object_i2 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i2 (M := M)))
theorem h_243 : Litex.Same (_object_i2 (M := M)) (_object_i2 (M := M)) :=
  (Litex.sameRefl (_object_i2 (M := M)))

noncomputable def _object_w11 := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.natural (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (1 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r ≤ _s)) (_object_i2 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_242 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))

theorem h_244 : (by
  let _equal_wd_1_0 := (_object_w11 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
  (let _equal_wd_1_0 := (_object_w11 (M := M));
  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (9 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (M.number (3 : ℂ))) = (M.number (9 : ℂ)) from by
    have _litex_residual : (M.powValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) = (M.number (9 : ℂ)) := (let _equal_wd_2_0 := (Litex.powNatReal (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
    (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (9 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (9 : ℂ)) ((3 : ℂ) ^ (2 : ℕ)) (9 : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ)) (by norm_num))))
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (M.number (3 : ℂ))))).trans (by
    let _litex_original := _equal_wd_1_0
    let _litex_literal := (let _wd_1_0 := (_object_i2 (M := M));
    let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
    (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.natural (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (1 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r ≤ _s)) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
      have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_243 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.integer Litex.StandardSetValue.natural (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (1 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r ≤ _s)) (fun (_raw_i3 : M.Value) => (M.powValue _raw_i3 (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.natural (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (1 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r ≤ _s)) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i3 : M.Value) => (M.powValue _raw_i3 (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.powValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) from rfl))
  ))).trans _litex_residual)))
end LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_integer_x5f_natural_x5f_square_x2f_statement_x2e_lit
