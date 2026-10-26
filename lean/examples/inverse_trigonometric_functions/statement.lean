import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_inverse_x5f_trigonometric_x5f_functions_x2f_statement_x2e_lit

universe u v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.realUnaryValue (M := M) Real.arctan _raw_i2)) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (Litex.arctan _value_i2 h_14)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.arctan _value_i2 h_14)
    exact (Litex.arctanInR _atomic_wd_1_0))))
theorem h_32 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_33 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_w5 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_32 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) True.intro)

theorem h_34 : (by
  let _equal_wd_1_0 := (_object_w5 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w5 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (0 : ℂ))) = (M.number (0 : ℂ)) from by
          have _litex_residual : ((Litex.realUnaryValue (M := M) Real.arctan) (M.number (0 : ℂ))) = (M.number (0 : ℂ)) := (let _equal_wd_2_0 := (Litex.arctan (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (0 : ℂ)) (Real.arctan ((0 : ℂ)).re : ℂ) (0 : ℂ) (let _trig := _equal_wd_2_0; Litex.denoteArctan _trig ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (0 : ℂ) _trig.wd (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num [Litex.nativeArccot, Real.arctan_zero, Complex.ofReal_div, Complex.ofReal_neg, neg_div]))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (0 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (0 : ℂ))) = ((Litex.realUnaryValue (M := M) Real.arctan) (M.number (0 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_33 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.realUnaryValue (M := M) Real.arctan _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (Litex.realUnaryValue (M := M) Real.arctan _raw_i2)) (Litex.denote _litex_literal.val.argument) = ((Litex.realUnaryValue (M := M) Real.arctan) (M.number (0 : ℂ))) from rfl))
        ))).trans _litex_residual)))
      )
  )

theorem h_75 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_88 : Litex.In _value_i3 (Litex.R (M := M))), (by
  let _object_w13 := (let _object_w8 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_32 (M := M)) h_88 True.intro);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w8 (h_32 (M := M)) (by
    let _atomic_wd_1_0 := _object_w8
    exact (by
      let _litex_return_call := _object_w8
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
  let _object_w14 := (let _wd_1_0 := (Litex.arctan _value_i3 h_88);
  (Litex.arctan _wd_1_0 (by
    let _atomic_wd_1_0 := (Litex.arctan _value_i3 h_88)
    exact (Litex.arctanInR _atomic_wd_1_0))))
  exact (by
    let _equal_wd_1_0 := _object_w13
    let _equal_wd_1_1 := _object_w14
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_88
          let _object_w13 := (let _object_w8 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_32 (M := M)) h_88 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w8 (h_32 (M := M)) (by
            let _atomic_wd_1_0 := _object_w8
            exact (by
              let _litex_return_call := _object_w8
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
          let _object_w14 := (let _wd_1_0 := (Litex.arctan _value_i3 h_88);
          (Litex.arctan _wd_1_0 (by
            let _atomic_wd_1_0 := (Litex.arctan _value_i3 h_88)
            exact (Litex.arctanInR _atomic_wd_1_0))))
          have h_74 : (by
            let _equal_wd_1_0 := _object_w13
            let _equal_wd_1_1 := _object_w14
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w13;
                  let _equal_wd_1_1 := _object_w14;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3))) = ((Litex.realUnaryValue (M := M) Real.arctan) ((Litex.realUnaryValue (M := M) Real.arctan) (Litex.denote _value_i3))) from by
                    have _litex_residual : ((Litex.realUnaryValue (M := M) Real.arctan) ((Litex.realUnaryValue (M := M) Real.arctan) (Litex.denote _value_i3))) = ((Litex.realUnaryValue (M := M) Real.arctan) ((Litex.realUnaryValue (M := M) Real.arctan) (Litex.denote _value_i3))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3))))).trans (congrArg (fun _x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _x) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3)) = ((Litex.realUnaryValue (M := M) Real.arctan) (Litex.denote _value_i3)) from by
                    let _litex_original := (_equal_wd_1_0).val.argument
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := _value_i3;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_88 True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_33 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.realUnaryValue (M := M) Real.arctan _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (Litex.realUnaryValue (M := M) Real.arctan _raw_i2)) (Litex.denote _litex_literal.val.argument) = ((Litex.realUnaryValue (M := M) Real.arctan) (Litex.denote _value_i3)) from rfl))
                  )))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) ((Litex.realUnaryValue (M := M) Real.arctan) (Litex.denote _value_i3))) = ((Litex.realUnaryValue (M := M) Real.arctan) ((Litex.realUnaryValue (M := M) Real.arctan) (Litex.denote _value_i3))) from by
                    let _litex_original := (let _object_w11 := (Litex.arctan _value_i3 h_88);
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w11 (h_32 (M := M)) (by
                      let _atomic_wd_1_0 := _object_w11
                      exact (Litex.arctanInR _atomic_wd_1_0)) True.intro))
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _object_w12 := (Litex.arctan _value_i3 h_88);
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _object_w12 (Litex.formulaFnInFnSet _wd_1_0) (by
                      let _atomic_wd_1_0 := _object_w12
                      exact (Litex.arctanInR _atomic_wd_1_0)) True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_33 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.realUnaryValue (M := M) Real.arctan _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (Litex.realUnaryValue (M := M) Real.arctan _raw_i2)) (Litex.denote _litex_literal.val.argument) = ((Litex.realUnaryValue (M := M) Real.arctan) ((Litex.realUnaryValue (M := M) Real.arctan) (Litex.denote _value_i3))) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          exact h_74
        )
      )
  )

noncomputable def _object_i4 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (((∃ (_r _s : ℝ), (M.negValue (M.number (1 : ℂ))) = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r ≤ _s)) ∧ ((∃ (_r _s : ℝ), _raw_i5 = M.number (_r : ℂ) ∧ (M.number (1 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)))) (fun (_raw_i5 : M.Value) => (Litex.realUnaryValue (M := M) Real.arcsin _raw_i5)) (by
  rintro _raw_i5 h_592 ⟨h_375, h_376⟩
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_592)
  have h_592 : Litex.In _value_i5 (Litex.R (M := M)) := h_592
  have h_375 : Litex.Le (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) _value_i5 :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_r _s : ℝ), (M.negValue (M.number (1 : ℂ))) = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r ≤ _s)
            exact h_375)
        )
    )
  have h_376 : Litex.Le _value_i5 (Litex.number (M := M) (1 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_r _s : ℝ), _raw_i5 = M.number (_r : ℂ) ∧ (M.number (1 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)
            exact h_376)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.arcsin _value_i5 h_592 (Litex.leOfSame (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (-1)) _value_i5 _value_i5 (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (show (- (1 : ℂ)) = (-1 : ℂ) from by norm_num))) rfl h_375) h_376)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.arcsin _value_i5 h_592 (Litex.leOfSame (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (-1)) _value_i5 _value_i5 (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (show (- (1 : ℂ)) = (-1 : ℂ) from by norm_num))) rfl h_375) h_376)
    exact (Litex.arcsinInR _atomic_wd_1_0))))
theorem h_852 : Litex.In (_object_i4 (M := M)) (Litex.fnSet ((_object_i4 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i4 (M := M)))
      )
  )
theorem h_853 : Litex.Same (_object_i4 (M := M)) (_object_i4 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i4 (M := M)))
      )
  )

noncomputable def _object_w27 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (((∃ (_r _s : ℝ), (M.negValue (M.number (1 : ℂ))) = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r ≤ _s)) ∧ ((∃ (_r _s : ℝ), _raw_i5 = M.number (_r : ℂ) ∧ (M.number (1 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)))) (_object_i4 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_852 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (And.intro (by
  let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
  exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (by
    let _atomic_wd_2_0 := _atomic_wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
    have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
    let _atomic_wd_2_0 := _atomic_wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))) = (-1 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
    let _atomic_wd_2_0 := _atomic_wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
      apply Complex.ofReal_injective
      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
  have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
  have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
    apply Complex.ofReal_injective
    exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))

theorem h_854 : (by
  let _equal_wd_1_0 := (_object_w27 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w27 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.number (0 : ℂ))) = (M.number (0 : ℂ)) from by
          have _litex_residual : ((Litex.realUnaryValue (M := M) Real.arcsin) (M.number (0 : ℂ))) = (M.number (0 : ℂ)) := (let _equal_wd_2_0 := (Litex.arcsin (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.leOfSame (Litex.number (M := M) (-1 : ℂ)) (Litex.number (-1)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (((Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))).trans (congrArg M.number (show (-1 : ℂ) = (-1 : ℂ) from by norm_num))) rfl ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (-1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (-1 : ℂ) (-1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (-1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (-1 : ℂ) (-1 : ℝ) (by norm_num)) = (-1 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (-1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (-1 : ℂ) (-1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (0 : ℂ)) (Real.arcsin ((0 : ℂ)).re : ℂ) (0 : ℂ) (let _trig := _equal_wd_2_0; Litex.denoteArcsin _trig ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (0 : ℂ) _trig.wd.1 (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num [Litex.nativeArccot, Real.arcsin_zero, Complex.ofReal_div, Complex.ofReal_neg, neg_div]))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.number (0 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.number (0 : ℂ))) = ((Litex.realUnaryValue (M := M) Real.arcsin) (M.number (0 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (((∃ (_r _s : ℝ), (M.negValue (M.number (1 : ℂ))) = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r ≤ _s)) ∧ ((∃ (_r _s : ℝ), _raw_i5 = M.number (_r : ℂ) ∧ (M.number (1 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (And.intro (by
            let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
            exact ((Litex.NativeBridge.le_iff_asReal _atomic_wd_1_0 _wd_1_1 (by
              let _atomic_wd_2_0 := _atomic_wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).mpr (by
              have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
              let _atomic_wd_2_0 := _atomic_wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))) = (-1 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
              let _atomic_wd_2_0 := _atomic_wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num))))).symm.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num))))
              have _litex_right_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                apply Complex.ofReal_injective
                exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
              exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) ((Litex.NativeBridge.le_iff_asReal _wd_1_1 (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_853 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (((∃ (_r _s : ℝ), (M.negValue (M.number (1 : ℂ))) = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r ≤ _s)) ∧ ((∃ (_r _s : ℝ), _raw_i5 = M.number (_r : ℂ) ∧ (M.number (1 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)))) (fun (_raw_i5 : M.Value) => (Litex.realUnaryValue (M := M) Real.arcsin _raw_i5)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (((∃ (_r _s : ℝ), (M.negValue (M.number (1 : ℂ))) = M.number (_r : ℂ) ∧ _raw_i5 = M.number (_s : ℂ) ∧ _r ≤ _s)) ∧ ((∃ (_r _s : ℝ), _raw_i5 = M.number (_r : ℂ) ∧ (M.number (1 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s)))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) => (Litex.realUnaryValue (M := M) Real.arcsin _raw_i5)) (Litex.denote _litex_literal.val.argument) = ((Litex.realUnaryValue (M := M) Real.arcsin) (M.number (0 : ℂ))) from rfl))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_i8 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ ((Litex.realUnaryValue (M := M) Real.cos _raw_i9) = (M.number (0 : ℂ))))) (fun (_raw_i9 : M.Value) => (Litex.realUnaryValue (M := M) Litex.nativeSec _raw_i9)) (by
  intro _raw_i9 h_2648 h_1220
  let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_2648)
  have h_2648 : Litex.In _value_i9 (Litex.R (M := M)) := h_2648
  have h_1220 : ¬ Litex.Same (Litex.cos _value_i9 h_2648) (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ ((Litex.realUnaryValue (M := M) Real.cos _raw_i9) = (M.number (0 : ℂ))))
            exact h_1220)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.sec _value_i9 h_2648 (by
      let _atomic_wd_2_0 := (Litex.cos _value_i9 h_2648)
      exact h_1220))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.sec _value_i9 h_2648 (by
      let _atomic_wd_2_0 := (Litex.cos _value_i9 h_2648)
      exact h_1220))
    exact (Litex.inRStar_base _atomic_wd_1_0 (Litex.secInRStar _atomic_wd_1_0)))))
theorem h_2694 : Litex.In (_object_i8 (M := M)) (Litex.fnSet ((_object_i8 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i8 (M := M)))
      )
  )
theorem h_2695 : Litex.Same (_object_i8 (M := M)) (_object_i8 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i8 (M := M)))
      )
  )

noncomputable def _object_w35 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ ((Litex.realUnaryValue (M := M) Real.cos _raw_i9) = (M.number (0 : ℂ))))) (_object_i8 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_2694 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
  let _atomic_wd_1_0 := (Litex.cos (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (Real.cos ((0 : ℂ)).re : ℂ) (0 : ℂ) (let _trig := _atomic_wd_1_0; Litex.denoteCos _trig ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (0 : ℂ) _trig.wd (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by have _angle : ((0 : ℂ)).re = (0) + (0 : ℤ) * (2 * Real.pi) := (by (conv_lhs => norm_num); ring); rw [_angle, Real.cos_add_int_mul_two_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div]))))

theorem h_2696 : (by
  let _equal_wd_1_0 := (_object_w35 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w35 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.number (0 : ℂ))) = (M.number (1 : ℂ)) from by
          have _litex_residual : ((Litex.realUnaryValue (M := M) Litex.nativeSec) (M.number (0 : ℂ))) = (M.number (1 : ℂ)) := (let _equal_wd_2_0 := (Litex.sec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
            let _atomic_wd_1_0 := (Litex.cos (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (Real.cos ((0 : ℂ)).re : ℂ) (0 : ℂ) (let _trig := _atomic_wd_1_0; Litex.denoteCos _trig ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (0 : ℂ) _trig.wd (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by have _angle : ((0 : ℂ)).re = (0) + (0 : ℤ) * (2 * Real.pi) := (by (conv_lhs => norm_num); ring); rw [_angle, Real.cos_add_int_mul_two_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div]))));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (1 : ℂ)) (Litex.nativeSec ((0 : ℂ)).re : ℂ) (1 : ℂ) (let _trig := _equal_wd_2_0; Litex.denoteSec _trig ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (0 : ℂ) _trig.wd.1 (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num [Litex.nativeSec]))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.number (0 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (M.number (0 : ℂ))) = ((Litex.realUnaryValue (M := M) Litex.nativeSec) (M.number (0 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i8 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ ((Litex.realUnaryValue (M := M) Real.cos _raw_i9) = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
            let _atomic_wd_1_0 := (Litex.cos _wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _wd_1_1 (Real.cos ((0 : ℂ)).re : ℂ) (0 : ℂ) (let _trig := _atomic_wd_1_0; Litex.denoteCos _trig ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _trig.val.arg (0 : ℂ) _trig.wd (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by have _angle : ((0 : ℂ)).re = (0) + (0 : ℤ) * (2 * Real.pi) := (by (conv_lhs => norm_num); ring); rw [_angle, Real.cos_add_int_mul_two_pi]; (conv_lhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); (conv_rhs => simp only [Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi]); norm_num [neg_div])))))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_2695 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ ((Litex.realUnaryValue (M := M) Real.cos _raw_i9) = (M.number (0 : ℂ))))) (fun (_raw_i9 : M.Value) => (Litex.realUnaryValue (M := M) Litex.nativeSec _raw_i9)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ ((Litex.realUnaryValue (M := M) Real.cos _raw_i9) = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i9 : M.Value) => (Litex.realUnaryValue (M := M) Litex.nativeSec _raw_i9)) (Litex.denote _litex_literal.val.argument) = ((Litex.realUnaryValue (M := M) Litex.nativeSec) (M.number (0 : ℂ))) from rfl))
        ))).trans _litex_residual)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_inverse_x5f_trigonometric_x5f_functions_x2f_statement_x2e_lit
