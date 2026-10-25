import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_double_x5f_reciprocal_x5f_composition_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by
  intro _raw_i2 h_43 h_1
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_43)
  have h_43 : Litex.In _value_i2 (Litex.R (M := M)) := h_43
  have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i2 = (M.number (0 : ℂ))))
            exact h_1)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_43) h_1)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_43) h_1)
    exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) h_43 (_atomic_wd_1_0).wd.2.2))))
theorem h_92 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_93 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_i4 := (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) (fun (_raw_i6 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i6))) (by
  intro _raw_i6 h_139 h_97
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_139)
  have h_139 : Litex.In _value_i6 (Litex.R (M := M)) := h_139
  have h_97 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i6 = (M.number (0 : ℂ))))
            exact h_97)
        )
    )
  change (by
    let _atomic_wd_1_0 := (let _object_w15 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i6 (h_92 (M := M)) h_139 h_97);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w15 (h_92 (M := M)) (by
      let _atomic_wd_2_0 := _object_w15
      exact (by
        let _litex_return_call := _object_w15
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
      let _atomic_wd_2_0 := _object_w15
      exact (by
        change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_2_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
        have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_139) h_97)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := (by
        let _atomic_wd_3_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_139) h_97)
        exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_139) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_97) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
        exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_139) h_97)) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from by
        have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from by
        let _litex_original := _object_w15
        let _litex_literal := (let _wd_2_0 := (_object_i1 (M := M));
        let _wd_2_1 := _value_i6;
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_139 h_97))
        have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
        have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
        exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from rfl))
      ))).trans _litex_residual)).symm)) _unfold_child
      ))))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w15 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i6 (h_92 (M := M)) h_139 h_97);
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w15 (h_92 (M := M)) (by
      let _atomic_wd_2_0 := _object_w15
      exact (by
        let _litex_return_call := _object_w15
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
      let _atomic_wd_2_0 := _object_w15
      exact (by
        change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_2_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
        have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_139) h_97)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := (by
        let _atomic_wd_3_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_139) h_97)
        exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_139) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_97) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
        exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_139) h_97)) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from by
        have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from by
        let _litex_original := _object_w15
        let _litex_literal := (let _wd_2_0 := (_object_i1 (M := M));
        let _wd_2_1 := _value_i6;
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_139 h_97))
        have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
        have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
        exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from rfl))
      ))).trans _litex_residual)).symm)) _unfold_child
      ))))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
Litex.compose (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (by
  have _composition_checked : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i6) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))).domain := (by
  intro _raw_i6 h_139 h_97
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_139)
  have h_139 : Litex.In _value_i6 (Litex.R (M := M)) := h_139
  have h_97 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i6 = (M.number (0 : ℂ))))
            exact h_97)
        )
    )
  let _composition_call := (let _object_w14 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i6 (h_92 (M := M)) h_139 h_97);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w14 (h_92 (M := M)) (by
  let _atomic_wd_1_0 := _object_w14
  exact (by
    let _litex_return_call := _object_w14
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
  let _atomic_wd_1_0 := _object_w14
  exact (by
    change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
    have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_139) h_97)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := (by
    let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_139) h_97)
    exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_139) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_97) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
    exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_139) h_97)) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from by
    have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from by
    let _litex_original := _object_w14
    let _litex_literal := (let _wd_2_0 := (_object_i1 (M := M));
    let _wd_2_1 := _value_i6;
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_139 h_97))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from rfl))
  ))).trans _litex_residual)).symm)) _unfold_child
  ))))
  exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
  intro _composition_input _preimage_domain
  obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _litex_input) _).mp _preimage_domain
  have _preimage_guard_0 := _preimage_guard
  have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
  exact _composition_checked _composition_input _preimage_members _preimage_guard_0))
theorem h_1858 : Litex.In (_object_i4 (M := M)) (let _checked_header : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _raw_i5) → True := (by
    intro _raw_i5 h_1851 h_973
    let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_1851)
    have h_1851 : Litex.In _value_i5 (Litex.R (M := M)) := h_1851
    have h_973 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i5 = (M.number (0 : ℂ))))
              exact h_973)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (0 : ℂ))))) (fun (_raw_i8 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i8))) (by
            intro _raw_i8 h_1017 h_975
            let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1017)
            have h_1017 : Litex.In _value_i8 (Litex.R (M := M)) := h_1017
            have h_975 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      change (¬ (_raw_i8 = (M.number (0 : ℂ))))
                      exact h_975)
                  )
              )
            change (by
              let _atomic_wd_2_0 := (let _object_w20 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i8 (h_92 (M := M)) h_1017 h_975);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w20 (h_92 (M := M)) (by
                let _atomic_wd_3_0 := _object_w20
                exact (by
                  let _litex_return_call := _object_w20
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
                let _atomic_wd_3_0 := _object_w20
                exact (by
                  change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_3_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
                  have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1017) h_975)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := (by
                  let _atomic_wd_4_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1017) h_975)
                  exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 h_1017) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_975) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                  exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1017) h_975)) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i8)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i8)) from by
                  have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i8)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i8)) := (show @Eq M.Value _ _ from Eq.refl _)
                  exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i8)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i8)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i8)) from by
                  let _litex_original := _object_w20
                  let _litex_literal := (let _wd_2_0 := (_object_i1 (M := M));
                  let _wd_2_1 := _value_i8;
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_1017 h_975))
                  have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                  have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                  exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i8)) from rfl))
                ))).trans _litex_residual)).symm)) _unfold_child
                ))))
              exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_2_0 := (let _object_w20 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i8 (h_92 (M := M)) h_1017 h_975);
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w20 (h_92 (M := M)) (by
                let _atomic_wd_3_0 := _object_w20
                exact (by
                  let _litex_return_call := _object_w20
                  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
                let _atomic_wd_3_0 := _object_w20
                exact (by
                  change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_3_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
                  have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1017) h_975)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := (by
                  let _atomic_wd_4_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1017) h_975)
                  exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 h_1017) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_975) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                  exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1017) h_975)) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i8)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i8)) from by
                  have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i8)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i8)) := (show @Eq M.Value _ _ from Eq.refl _)
                  exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i8)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i8)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i8)) from by
                  let _litex_original := _object_w20
                  let _litex_literal := (let _wd_2_0 := (_object_i1 (M := M));
                  let _wd_2_1 := _value_i8;
                  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_1017 h_975))
                  have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                  have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                  exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i8)) from rfl))
                ))).trans _litex_residual)).symm)) _unfold_child
                ))))
              exact (by
                let _litex_return_call := _atomic_wd_2_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
          Litex.compose (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (by
            have _composition_checked : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i8 : M.Value) => (¬ (_raw_i8 = (M.number (0 : ℂ))))) _raw_i8) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i8) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))).domain := (by
            intro _raw_i8 h_1017 h_975
            let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_1017)
            have h_1017 : Litex.In _value_i8 (Litex.R (M := M)) := h_1017
            have h_975 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      change (¬ (_raw_i8 = (M.number (0 : ℂ))))
                      exact h_975)
                  )
              )
            let _composition_call := (let _object_w19 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i8 (h_92 (M := M)) h_1017 h_975);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w19 (h_92 (M := M)) (by
            let _atomic_wd_2_0 := _object_w19
            exact (by
              let _litex_return_call := _object_w19
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
            let _atomic_wd_2_0 := _object_w19
            exact (by
              change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_2_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
              have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1017) h_975)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := (by
              let _atomic_wd_3_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1017) h_975)
              exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 h_1017) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_975) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
              exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i8 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1017) h_975)) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i8)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i8)) from by
              have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i8)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i8)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i8)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i8)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i8)) from by
              let _litex_original := _object_w19
              let _litex_literal := (let _wd_2_0 := (_object_i1 (M := M));
              let _wd_2_1 := _value_i8;
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_1017 h_975))
              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i8)) from rfl))
            ))).trans _litex_residual)).symm)) _unfold_child
            ))))
            exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
            intro _composition_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _litex_input) _).mp _preimage_domain
            have _preimage_guard_0 := _preimage_guard
            have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
            exact _composition_checked _composition_input _preimage_members _preimage_guard_0))
          let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _raw_i5) → True := (by
              intro _raw_i5 h_1851 h_973
              let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_1851)
              have h_1851 : Litex.In _value_i5 (Litex.R (M := M)) := h_1851
              have h_973 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i5 = (M.number (0 : ℂ))))
                        exact h_973)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ)))))))
          exact (Litex.composeInFnSet _atomic_wd_1_0 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))))
      )
  )
theorem h_1859 : Litex.Same (_object_i4 (M := M)) (_object_i4 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (let _composition_lambda := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) (fun (_raw_i6 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i6))) (by
          intro _raw_i6 h_139 h_97
          let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_139)
          have h_139 : Litex.In _value_i6 (Litex.R (M := M)) := h_139
          have h_97 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                    exact h_97)
                )
            )
          change (by
            let _atomic_wd_1_0 := (let _object_w15 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i6 (h_92 (M := M)) h_139 h_97);
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w15 (h_92 (M := M)) (by
              let _atomic_wd_2_0 := _object_w15
              exact (by
                let _litex_return_call := _object_w15
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
              let _atomic_wd_2_0 := _object_w15
              exact (by
                change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_2_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
                have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_139) h_97)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := (by
                let _atomic_wd_3_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_139) h_97)
                exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_139) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_97) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_139) h_97)) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from by
                have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
                exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from by
                let _litex_original := _object_w15
                let _litex_literal := (let _wd_2_0 := (_object_i1 (M := M));
                let _wd_2_1 := _value_i6;
                (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_139 h_97))
                have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from rfl))
              ))).trans _litex_residual)).symm)) _unfold_child
              ))))
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
          exact (by
            let _atomic_wd_1_0 := (let _object_w15 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i6 (h_92 (M := M)) h_139 h_97);
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w15 (h_92 (M := M)) (by
              let _atomic_wd_2_0 := _object_w15
              exact (by
                let _litex_return_call := _object_w15
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
              let _atomic_wd_2_0 := _object_w15
              exact (by
                change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_2_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
                have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_139) h_97)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := (by
                let _atomic_wd_3_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_139) h_97)
                exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_139) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_97) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_139) h_97)) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from by
                have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
                exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from by
                let _litex_original := _object_w15
                let _litex_literal := (let _wd_2_0 := (_object_i1 (M := M));
                let _wd_2_1 := _value_i6;
                (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_139 h_97))
                have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from rfl))
              ))).trans _litex_residual)).symm)) _unfold_child
              ))))
            exact (by
              let _litex_return_call := _atomic_wd_1_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))));
        Litex.compose (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (by
          have _composition_checked : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i6) ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))).domain := (by
          intro _raw_i6 h_139 h_97
          let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_139)
          have h_139 : Litex.In _value_i6 (Litex.R (M := M)) := h_139
          have h_97 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                    exact h_97)
                )
            )
          let _composition_call := (let _object_w14 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _value_i6 (h_92 (M := M)) h_139 h_97);
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w14 (h_92 (M := M)) (by
          let _atomic_wd_1_0 := _object_w14
          exact (by
            let _litex_return_call := _object_w14
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
          let _atomic_wd_1_0 := _object_w14
          exact (by
            change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (0 : ℂ)))
            have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_139) h_97)) (Litex.denote (Litex.number (M := M) (0 : ℂ))) := (by
            let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_139) h_97)
            exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_139) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_97) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
            exact Eq.mp (((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_139) h_97)) (Litex.denote (Litex.number (M := M) (0 : ℂ)))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (¬ (_unfold_arg0 = _unfold_arg1))) _unfold_value (Litex.denote (Litex.number (M := M) (0 : ℂ)))) ((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from by
            have _litex_residual : (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from by
            let _litex_original := _object_w14
            let _litex_literal := (let _wd_2_0 := (_object_i1 (M := M));
            let _wd_2_1 := _value_i6;
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_2_0 _wd_2_1 (Litex.formulaFnInFnSet _wd_2_0) h_139 h_97))
            have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
            have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from rfl))
          ))).trans _litex_residual)).symm)) _unfold_child
          ))))
          exact Litex.callInputInDomain _composition_call (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))
          intro _composition_input _preimage_domain
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _litex_input) _).mp _preimage_domain
          have _preimage_guard_0 := _preimage_guard
          have _preimage_base : M.mem _composition_input (Litex.denote (Litex.R (M := M))) := _preimage_members
          exact _composition_checked _composition_input _preimage_members _preimage_guard_0)))
      )
  )

noncomputable def _object_w27 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => (¬ (_raw_i12 = (M.number (0 : ℂ))))) (_object_i4 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.inOfSame (_object_i4 (M := M)) (_object_i4 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => (¬ (_raw_i12 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i12 : M.Value) => (¬ (_raw_i12 = (M.number (0 : ℂ))))))) ((h_1859 (M := M))).symm (Litex.sameRefl _) (Litex.composeInFnSet (_object_i4 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_1860 : (by
  let _equal_wd_1_0 := (_object_w27 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.number (2 : ℂ))) = (M.number (2 : ℂ)) from by
          have _litex_residual : (M.divValue (M.number (1 : ℂ)) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))) = (M.number (2 : ℂ)) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
          let _wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (2 : ℂ)) = ((1 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (2 : ℂ))))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (2 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (2 : ℂ)) ((1 : ℂ) / ((1 : ℂ) / (2 : ℂ))) (2 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_0).val.right (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2.1 (_equal_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_2_0).val.right).wd.1 ((_equal_wd_2_0).val.right).wd.2.1 ((_equal_wd_2_0).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))))
          exact ((((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.number (2 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.number (2 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ)))) from by
          have _composition_head := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.number (M := M) (2 : ℂ)))) (show (Litex.denote (_object_i4 (M := M))) = Litex.denote (_object_i4 (M := M)) from (h_1859 (M := M)))
          exact _composition_head.trans (Litex.composeCall (_object_i4 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))))) ((h_93 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote (Litex.number (M := M) (2 : ℂ))) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i15 : M.Value) => (¬ (_raw_i15 = (M.number (0 : ℂ))))) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))⟩))))).trans (congrArg (fun _x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _x) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) from by
          let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_92 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) from rfl))
        )))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))) = (M.divValue (M.number (1 : ℂ)) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))) from by
          let _litex_original := (let _object_w25 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (_object_i1 (M := M)) _object_w25 (h_92 (M := M)) (by
            let _atomic_wd_1_0 := _object_w25
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w25).wd.1 (_object_w25).wd.2.1 (_object_w25).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num)))) (by
            let _atomic_wd_1_0 := _object_w25
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w25).wd.1 (_object_w25).wd.2.1 (_object_w25).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))))
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
          let _object_w26 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _wd_1_0 _object_w26 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w26
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w26).wd.1 (_object_w26).wd.2.1 (_object_w26).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num)))) (by
            let _atomic_wd_1_0 := _object_w26
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w26).wd.1 (_object_w26).wd.2.1 (_object_w26).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_93 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))) from rfl))
        ))).trans _litex_residual)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_double_x5f_reciprocal_x5f_composition_x2f_statement_x2e_lit
