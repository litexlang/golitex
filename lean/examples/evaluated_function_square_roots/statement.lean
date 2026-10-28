import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_function_x5f_square_x5f_roots_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.mulValue _raw_i2 _raw_i2)) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i2 (M.real_subset_complex _ h_14) (M.real_subset_complex _ h_14))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i2 (M.real_subset_complex _ h_14) (M.real_subset_complex _ h_14))
    exact (Litex.mulInR _value_i2 _value_i2 h_14 h_14))))
theorem h_68 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_69 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_886 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_68 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro);
  (Litex.sqrt _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
    let _atomic_wd_1_1 := _wd_1_0
    exact (by
      change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.denote _atomic_wd_1_1)
      have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.denote (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))) := (by
      let _atomic_wd_2_1 := (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
      exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
        let _atomic_wd_3_0 := _atomic_wd_2_1
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num))))).mpr (by
        have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
          apply Complex.ofReal_injective
          exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
        have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_2_1 (by
        let _atomic_wd_3_0 := _atomic_wd_2_1
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num)))) = (9 : ℝ) := by
          apply Complex.ofReal_injective
          exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_1 (by
        let _atomic_wd_3_0 := _atomic_wd_2_1
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num))))
        exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
      exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.denote (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) _unfold_value) ((let _equal_wd_2_0 := _atomic_wd_1_1;
    let _equal_wd_2_1 := (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
    (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))) = (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) from by
      have _litex_residual : (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) = (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))) = (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) from by
      let _litex_original := _equal_wd_2_0
      let _litex_literal := (let _wd_2_0 := (_object_i1 (M := M));
      let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro))
      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_69 (M := M)) (Litex.sameRefl _litex_original.val.argument)
      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.mulValue _raw_i2 _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.mulValue _raw_i2 _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) from rfl))
    ))).trans _litex_residual)))).symm)) _unfold_child
    ))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_68 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro);
        (Litex.sqrt _wd_1_0 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (by
            let _litex_return_call := _atomic_wd_1_0
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
          let _atomic_wd_1_1 := _wd_1_0
          exact (by
            change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.denote _atomic_wd_1_1)
            have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.denote (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))) := (by
            let _atomic_wd_2_1 := (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
            exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
              let _atomic_wd_3_0 := _atomic_wd_2_1
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num))))).mpr (by
              have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
              have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_2_1 (by
              let _atomic_wd_3_0 := _atomic_wd_2_1
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num)))) = (9 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_1 (by
              let _atomic_wd_3_0 := _atomic_wd_2_1
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num))))
              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
            exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.denote (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) _unfold_value) ((let _equal_wd_2_0 := _atomic_wd_1_1;
          let _equal_wd_2_1 := (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
          (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))) = (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) from by
            have _litex_residual : (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) = (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))) = (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) from by
            let _litex_original := _equal_wd_2_0
            let _litex_literal := (let _wd_2_0 := (_object_i1 (M := M));
            let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro))
            have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_69 (M := M)) (Litex.sameRefl _litex_original.val.argument)
            have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.mulValue _raw_i2 _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.mulValue _raw_i2 _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) from rfl))
          ))).trans _litex_residual)))).symm)) _unfold_child
          ))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.sqrtValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ)))) from congrArg (Litex.sqrtValue (M := M)) (show Litex.denote (_equal_wd_1_0).val.arg = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl))) (((Eq.refl (Litex.sqrtValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ)))))).trans (show (Litex.sqrtValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ)))) = M.number (3 : ℂ) from (congrArg (Litex.sqrtValue (M := M)) (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))) = (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) from by
          let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_68 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro)
          let _litex_formula := (_object_i1 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_69 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _).mpr _litex_original.wd.2)
          exact (Eq.symm (show Litex.denote (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_68 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl))).trans (_litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) from congrArg (fun (_raw_i2 : M.Value) => (M.mulValue _raw_i2 _raw_i2)) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl))))
        )).trans (((Eq.refl (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))))).trans (show (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) = M.number (9 : ℂ) from ((congrArg₂ M.mulValue (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.mul_numbers (3 : ℂ) (3 : ℂ)).trans (congrArg M.number (by norm_num)))))))).trans (by
          have _argument : (9 : ℂ) = (((9 : ℝ) : ℝ) : ℂ) := by norm_num
          have _root : Real.sqrt (9 : ℝ) = (3 : ℝ) := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
          have _cast : (((3 : ℝ) : ℝ) : ℂ) = (3 : ℂ) := by norm_num
          exact (congrArg (fun x : ℂ => Litex.sqrtValue (M := M) (M.number x)) _argument).trans ((Litex.sqrtValue_number (M := M) (9 : ℝ)).trans (congrArg M.number ((congrArg (fun x : ℝ => (x : ℂ)) _root).trans _cast)))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))).symm)))
      )
  )

theorem h_1700 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_68 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro);
  (Litex.sqrt _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
    let _atomic_wd_1_1 := _wd_1_0
    exact (by
      change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.denote _atomic_wd_1_1)
      have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.denote (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))) := (by
      let _atomic_wd_2_1 := (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
      exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
        let _atomic_wd_3_0 := _atomic_wd_2_1
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num))))).mpr (by
        have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
          apply Complex.ofReal_injective
          exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
        have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_2_1 (by
        let _atomic_wd_3_0 := _atomic_wd_2_1
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num)))) = (9 : ℝ) := by
          apply Complex.ofReal_injective
          exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_2_1 (by
        let _atomic_wd_3_0 := _atomic_wd_2_1
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 ((3 : ℂ) * (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_3_0).wd.1 (_atomic_wd_3_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) * (3 : ℂ)) (9 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteMul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num))))
        exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
      exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.denote (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) _unfold_value) ((let _equal_wd_2_0 := _atomic_wd_1_1;
    let _equal_wd_2_1 := (Litex.mul (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
    (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))) = (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) from by
      have _litex_residual : (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) = (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (3 : ℂ))) = (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) from by
      let _litex_original := _equal_wd_2_0
      let _litex_literal := (let _wd_2_0 := (_object_i1 (M := M));
      let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro))
      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_69 (M := M)) (Litex.sameRefl _litex_original.val.argument)
      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.mulValue _raw_i2 _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.mulValue _raw_i2 _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.mulValue (M.number (3 : ℂ)) (M.number (3 : ℂ))) from rfl))
    ))).trans _litex_residual)))).symm)) _unfold_child
    ))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_886 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_function_x5f_square_x5f_roots_x2f_statement_x2e_lit
