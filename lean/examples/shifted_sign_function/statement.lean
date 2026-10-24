import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_shifted_x5f_sign_x5f_function_x2f_statement_x2e_lit

universe u v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.signValue (M := M) _raw_i2)) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (Litex.sign _value_i2 h_14)
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.sign _value_i2 h_14)
    exact (Litex.signInZ _atomic_wd_1_0))))
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

noncomputable def _object_i3 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.subValue _raw_i4 (M.number (2 : ℂ)))) (by
  intro _raw_i4 h_47 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_47)
  have h_47 : Litex.In _value_i4 (Litex.R (M := M)) := h_47
  change (by
    let _atomic_wd_1_0 := (Litex.sub _value_i4 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_47) (Litex.numberInC (M := M) (2 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.sub _value_i4 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_47) (Litex.numberInC (M := M) (2 : ℂ)))
    exact (Litex.subInR _value_i4 (Litex.number (M := M) (2 : ℂ)) h_47 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))))))
theorem h_101 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i3 (M := M)))
      )
  )
theorem h_102 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i3 (M := M)))
      )
  )

noncomputable def _object_i5 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (Litex.signValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i6))) (by
  intro _raw_i6 h_116 _
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_116)
  have h_116 : Litex.In _value_i6 (Litex.R (M := M)) := h_116
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i6 (h_101 (M := M)) h_116 True.intro);
    (Litex.sign _wd_1_0 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (by
        let _litex_return_call := _atomic_wd_2_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i6 (h_101 (M := M)) h_116 True.intro);
    (Litex.sign _wd_1_0 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (by
        let _litex_return_call := _atomic_wd_2_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))
    exact (Litex.signInZ _atomic_wd_1_0))))
theorem h_294 : Litex.In (_object_i5 (M := M)) (Litex.fnSet ((_object_i5 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i5 (M := M)))
      )
  )
theorem h_295 : Litex.Same (_object_i5 (M := M)) (_object_i5 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i5 (M := M)))
      )
  )

noncomputable def _object_w22 := (let _object_w13 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w13 (h_32 (M := M)) (by
  let _atomic_wd_1_0 := _object_w13
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_object_w13).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (3 : ℂ)) (-3 : ℝ) (by norm_num)))) True.intro))

noncomputable def _object_w23 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))

theorem h_296 : (by
  let _equal_wd_1_0 := (_object_w22 (M := M))
  let _equal_wd_1_1 := (_object_w23 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w22 (M := M));
        let _equal_wd_1_1 := (_object_w23 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.negValue (M.number (3 : ℂ)))) = (M.negValue (M.number (1 : ℂ))) from by
          have _litex_residual : ((Litex.signValue (M := M)) (M.negValue (M.number (3 : ℂ)))) = (M.negValue (M.number (1 : ℂ))) := (let _equal_wd_2_0 := (let _wd_1_0 := (_equal_wd_1_0).val.argument;
          (Litex.sign _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (3 : ℂ)) (-3 : ℝ) (by norm_num))))));
          let _equal_wd_2_1 := _equal_wd_1_1;
          (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 _equal_wd_2_1 (-1 : ℂ) (- (1 : ℂ)) (let _sign := _equal_wd_2_0;
          let _member : Litex.In _sign Litex.C := Litex.integerToComplex _sign (Litex.signInZ _sign);
          (Litex.signDenoteReal _sign (-3 : ℝ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) ((_equal_wd_2_0).val.arg).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : (- (3 : ℂ)) = (((-3 : ℝ) : ℝ) : ℂ))))).trans (congrArg M.number (by norm_num [Real.sign] : ((Real.sign (-3 : ℝ) : ℝ) : ℂ) = (-1 : ℂ)))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.negValue (M.number (3 : ℂ)))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.negValue (M.number (3 : ℂ)))) = ((Litex.signValue (M := M)) (M.negValue (M.number (3 : ℂ)))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
          let _object_w21 := (_equal_wd_1_0).val.argument;
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _wd_1_0 _object_w21 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w21
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_object_w21).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (3 : ℂ)) (-3 : ℝ) (by norm_num)))) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_33 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.signValue (M := M) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (Litex.signValue (M := M) _raw_i2)) (Litex.denote _litex_literal.val.argument) = ((Litex.signValue (M := M)) (M.negValue (M.number (3 : ℂ)))) from rfl))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_w24 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (0 : ℂ)) (h_32 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) True.intro)

theorem h_640 : (by
  let _equal_wd_1_0 := (_object_w24 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w24 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (0 : ℂ))) = (M.number (0 : ℂ)) from by
          have _litex_residual : ((Litex.signValue (M := M)) (M.number (0 : ℂ))) = (M.number (0 : ℂ)) := (let _equal_wd_2_0 := (Litex.sign (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (0 : ℂ)) (0 : ℂ) (0 : ℂ) (let _sign := _equal_wd_2_0;
          let _member : Litex.In _sign Litex.C := Litex.integerToComplex _sign (Litex.signInZ _sign);
          (Litex.signDenoteReal _sign (0 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (((0 : ℝ) : ℝ) : ℂ))))).trans (congrArg M.number (by norm_num [Real.sign] : ((Real.sign (0 : ℝ) : ℝ) : ℂ) = (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (0 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (0 : ℂ))) = ((Litex.signValue (M := M)) (M.number (0 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_33 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.signValue (M := M) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (Litex.signValue (M := M) _raw_i2)) (Litex.denote _litex_literal.val.argument) = ((Litex.signValue (M := M)) (M.number (0 : ℂ))) from rfl))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_w26 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (4 : ℂ)) (h_32 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) True.intro)

theorem h_698 : (by
  let _equal_wd_1_0 := (_object_w26 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w26 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (4 : ℂ))) = (M.number (1 : ℂ)) from by
          have _litex_residual : ((Litex.signValue (M := M)) (M.number (4 : ℂ))) = (M.number (1 : ℂ)) := (let _equal_wd_2_0 := (Litex.sign (Litex.number (M := M) (4 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (let _sign := _equal_wd_2_0;
          let _member : Litex.In _sign Litex.C := Litex.integerToComplex _sign (Litex.signInZ _sign);
          (Litex.signDenoteReal _sign (4 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num : (4 : ℂ) = (((4 : ℝ) : ℝ) : ℂ))))).trans (congrArg M.number (by norm_num [Real.sign] : ((Real.sign (4 : ℝ) : ℝ) : ℂ) = (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (4 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (4 : ℂ))) = ((Litex.signValue (M := M)) (M.number (4 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_33 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.signValue (M := M) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (Litex.signValue (M := M) _raw_i2)) (Litex.denote _litex_literal.val.argument) = ((Litex.signValue (M := M)) (M.number (4 : ℂ))) from rfl))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_w28 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (_object_i5 (M := M)) (Litex.number (M := M) (1 : ℂ)) (h_294 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro)

theorem h_753 : (by
  let _equal_wd_1_0 := (_object_w28 (M := M))
  let _equal_wd_1_1 := (_object_w23 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w28 (M := M));
        let _equal_wd_1_1 := (_object_w23 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (M.number (1 : ℂ))) = (M.negValue (M.number (1 : ℂ))) from by
          have _litex_residual : ((Litex.signValue (M := M)) (M.subValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))) = (M.negValue (M.number (1 : ℂ))) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.sub (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
          (Litex.sign _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) - (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) - (2 : ℂ)) (-1 : ℝ) (by norm_num))))));
          let _equal_wd_2_1 := (_object_w23 (M := M));
          (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 _equal_wd_2_1 (-1 : ℂ) (- (1 : ℂ)) (let _sign := _equal_wd_2_0;
          let _member : Litex.In _sign Litex.C := Litex.integerToComplex _sign (Litex.signInZ _sign);
          (Litex.signDenoteReal _sign (-1 : ℝ) (((Litex.NativeBridge.denoteSub (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_2_0).val.arg).wd.1 ((_equal_wd_2_0).val.arg).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) - (2 : ℂ)) = (((-1 : ℝ) : ℝ) : ℂ))))).trans (congrArg M.number (by norm_num [Real.sign] : ((Real.sign (-1 : ℝ) : ℝ) : ℂ) = (-1 : ℂ)))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) ((_object_w23 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by norm_num))))
          exact ((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (M.number (1 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (M.number (1 : ℂ))) = ((Litex.signValue (M := M)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (1 : ℂ)))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i5 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_295 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (Litex.signValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i6))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i6 : M.Value) => (Litex.signValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i6))) (Litex.denote _litex_literal.val.argument) = ((Litex.signValue (M := M)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (1 : ℂ)))) from rfl))
        ))).trans (congrArg (Litex.signValue (M := M)) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (1 : ℂ))) = (M.subValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) from by
          let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (1 : ℂ)) (h_101 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro)
          let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_102 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.subValue _raw_i4 (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.subValue _raw_i4 (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.subValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) from rfl))
        )))).trans _litex_residual)))
      )
  )

noncomputable def _object_w29 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (_object_i5 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_294 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)

theorem h_1097 : (by
  let _equal_wd_1_0 := (_object_w29 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w29 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (M.number (2 : ℂ))) = (M.number (0 : ℂ)) from by
          have _litex_residual : ((Litex.signValue (M := M)) (M.subValue (M.number (2 : ℂ)) (M.number (2 : ℂ)))) = (M.number (0 : ℂ)) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.sub (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
          (Litex.sign _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((2 : ℂ) - (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) - (2 : ℂ)) (0 : ℝ) (by norm_num))))));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (0 : ℂ)) (0 : ℂ) (0 : ℂ) (let _sign := _equal_wd_2_0;
          let _member : Litex.In _sign Litex.C := Litex.integerToComplex _sign (Litex.signInZ _sign);
          (Litex.signDenoteReal _sign (0 : ℝ) (((Litex.NativeBridge.denoteSub (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_2_0).val.arg).wd.1 ((_equal_wd_2_0).val.arg).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) - (2 : ℂ)) = (((0 : ℝ) : ℝ) : ℂ))))).trans (congrArg M.number (by norm_num [Real.sign] : ((Real.sign (0 : ℝ) : ℝ) : ℂ) = (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
          exact ((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (M.number (2 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (M.number (2 : ℂ))) = ((Litex.signValue (M := M)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (2 : ℂ)))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i5 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_295 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (Litex.signValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i6))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i6 : M.Value) => (Litex.signValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i6))) (Litex.denote _litex_literal.val.argument) = ((Litex.signValue (M := M)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (2 : ℂ)))) from rfl))
        ))).trans (congrArg (Litex.signValue (M := M)) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (2 : ℂ))) = (M.subValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) from by
          let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_101 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)
          let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_102 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.subValue _raw_i4 (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.subValue _raw_i4 (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.subValue (M.number (2 : ℂ)) (M.number (2 : ℂ))) from rfl))
        )))).trans _litex_residual)))
      )
  )

noncomputable def _object_w30 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (_object_i5 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_294 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro)

theorem h_1235 : (by
  let _equal_wd_1_0 := (_object_w30 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w30 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (M.number (3 : ℂ))) = (M.number (1 : ℂ)) from by
          have _litex_residual : ((Litex.signValue (M := M)) (M.subValue (M.number (3 : ℂ)) (M.number (2 : ℂ)))) = (M.number (1 : ℂ)) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.sub (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
          (Litex.sign _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) - (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) - (2 : ℂ)) (1 : ℝ) (by norm_num))))));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (let _sign := _equal_wd_2_0;
          let _member : Litex.In _sign Litex.C := Litex.integerToComplex _sign (Litex.signInZ _sign);
          (Litex.signDenoteReal _sign (1 : ℝ) (((Litex.NativeBridge.denoteSub (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_2_0).val.arg).wd.1 ((_equal_wd_2_0).val.arg).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) - (2 : ℂ)) = (((1 : ℝ) : ℝ) : ℂ))))).trans (congrArg M.number (by norm_num [Real.sign] : ((Real.sign (1 : ℝ) : ℝ) : ℂ) = (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
          exact ((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (M.number (3 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (M.number (3 : ℂ))) = ((Litex.signValue (M := M)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (3 : ℂ)))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i5 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_295 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (Litex.signValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i6))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i6 : M.Value) => (Litex.signValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i6))) (Litex.denote _litex_literal.val.argument) = ((Litex.signValue (M := M)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (3 : ℂ)))) from rfl))
        ))).trans (congrArg (Litex.signValue (M := M)) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (3 : ℂ))) = (M.subValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) from by
          let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_101 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro)
          let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_102 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.subValue _raw_i4 (M.number (2 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.subValue _raw_i4 (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.subValue (M.number (3 : ℂ)) (M.number (2 : ℂ))) from rfl))
        )))).trans _litex_residual)))
      )
  )

theorem h_1372 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_1375 : Litex.In _value_i7 (Litex.R (M := M))) (h_1370 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i7), (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i7 (h_32 (M := M)) h_1375 True.intro)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_1375 h_1370
          have h_1395 : Litex.In _value_i7 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_1375
                )
            )
          let _object_w33 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i7 (h_32 (M := M)) h_1395 True.intro)

          let _object_w34 := (Litex.sign _value_i7 h_1395)

          have h_1373 : (by
            let _equal_wd_1_0 := _object_w33
            let _equal_wd_1_1 := _object_w34
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w33;
                  let _equal_wd_1_1 := _object_w34;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i7)) = ((Litex.signValue (M := M)) (Litex.denote _value_i7)) from by
                    have _litex_residual : ((Litex.signValue (M := M)) (Litex.denote _value_i7)) = ((Litex.signValue (M := M)) (Litex.denote _value_i7)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i7)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i7)) = ((Litex.signValue (M := M)) (Litex.denote _value_i7)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := _value_i7;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_1395 True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_33 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.signValue (M := M) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (Litex.signValue (M := M) _raw_i2)) (Litex.denote _litex_literal.val.argument) = ((Litex.signValue (M := M)) (Litex.denote _value_i7)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          have h_1374 : (by
            let _equal_wd_1_0 := _object_w34
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w34;
                  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from ((Litex.signOfPositive _equal_wd_1_0 h_1370).trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))).symm)))
                )
            )
          exact ((h_1373).trans h_1374)
        )
      )
  )

theorem h_1496 : (by
  have h_1497 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))
        )
    )
  exact (by
    let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (5 : ℂ)) (h_32 (M := M)) h_1497 True.intro)
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_1497 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))
                )
            )
          have h_1498 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) h_1497).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (5 : ℂ)) h_1497 = (5 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (5 : ℂ)) h_1497).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))
                )
            )
          have h_1499 : Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (5 : ℂ)) (h_32 (M := M)) h_1497 True.intro) (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_1372 (M := M)) (Litex.number (M := M) (5 : ℂ)) h_1497 h_1498)
                )
            )
          exact (let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (5 : ℂ)) (h_32 (M := M)) h_1497 True.intro);
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_1499).trans (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_shifted_x5f_sign_x5f_function_x2f_statement_x2e_lit
