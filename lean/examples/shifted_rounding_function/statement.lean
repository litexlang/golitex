import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_shifted_x5f_rounding_x5f_function_x2f_statement_x2e_lit

universe u v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.roundingValue (M := M) false _raw_i2)) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (Litex.floor _value_i2 h_14)
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.floor _value_i2 h_14)
    exact (Litex.roundingInZ _atomic_wd_1_0))))
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

noncomputable def _object_i3 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))) (by
  intro _raw_i4 h_47 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_47)
  have h_47 : Litex.In _value_i4 (Litex.R (M := M)) := h_47
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := _value_i4;
    let _wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    (Litex.add _wd_1_0 _wd_1_1 (M.real_subset_complex _ h_47) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (2 : ℂ)) = ((1 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (2 : ℂ)))))))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := _value_i4;
    let _wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    (Litex.add _wd_1_0 _wd_1_1 (M.real_subset_complex _ h_47) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (2 : ℂ)) = ((1 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (2 : ℂ)))))))
    exact (Litex.addInR _value_i4 (_atomic_wd_1_0).val.right h_47 (Litex.NativeBridge.inOfDenoteNumber (_atomic_wd_1_0).val.right ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num)))))))
theorem h_145 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i3 (M := M)))
      )
  )
theorem h_146 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i3 (M := M)))
      )
  )

noncomputable def _object_i5 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (Litex.roundingValue (M := M) true (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i6))) (by
  intro _raw_i6 h_160 _
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_160)
  have h_160 : Litex.In _value_i6 (Litex.R (M := M)) := h_160
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i6 (h_145 (M := M)) h_160 True.intro);
    (Litex.ceil _wd_1_0 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (by
        let _litex_return_call := _atomic_wd_2_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i6 (h_145 (M := M)) h_160 True.intro);
    (Litex.ceil _wd_1_0 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (by
        let _litex_return_call := _atomic_wd_2_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))
    exact (Litex.roundingInZ _atomic_wd_1_0))))
theorem h_338 : Litex.In (_object_i5 (M := M)) (Litex.fnSet ((_object_i5 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i5 (M := M)))
      )
  )
theorem h_339 : Litex.Same (_object_i5 (M := M)) (_object_i5 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i5 (M := M)))
      )
  )

noncomputable def _object_w20 := (let _object_w13 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (_object_i5 (M := M)) _object_w13 (h_338 (M := M)) (by
  let _atomic_wd_1_0 := _object_w13
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w13).wd.1 (_object_w13).wd.2.1 (_object_w13).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro))

theorem h_340 : (by
  let _equal_wd_1_0 := (_object_w20 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w20 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))) = (M.number (1 : ℂ)) from by
          have _litex_residual : ((Litex.roundingValue (M := M) true) (M.addValue (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))) = (M.number (1 : ℂ)) := (let _equal_wd_2_0 := (let _wd_1_0 := (let _wd_2_0 := (_equal_wd_1_0).val.argument;
          let _wd_2_1 := _wd_2_0;
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (2 : ℂ)) = ((1 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (2 : ℂ))))) (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (2 : ℂ)) = ((1 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (2 : ℂ)))))));
          (Litex.ceil _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (((1 : ℂ) / (2 : ℂ)) + ((1 : ℂ) / (2 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_1_0).val.left).wd.1 ((_atomic_wd_1_0).val.left).wd.2.1 ((_atomic_wd_1_0).val.left).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_1_0).val.right).wd.1 ((_atomic_wd_1_0).val.right).wd.2.1 ((_atomic_wd_1_0).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (Litex.NativeBridge.numberInROfEq (((1 : ℂ) / (2 : ℂ)) + ((1 : ℂ) / (2 : ℂ))) (1 : ℝ) (by norm_num))))));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (let _round := _equal_wd_2_0;
          let _member : Litex.In _round Litex.C := Litex.integerToComplex _round (Litex.roundingInZ _round);
          (Litex.roundingDenoteReal _round (1 : ℝ) (((Litex.NativeBridge.denoteAdd ((_equal_wd_2_0).val.arg).val.left ((_equal_wd_2_0).val.arg).val.right ((_equal_wd_2_0).val.arg).wd.1 ((_equal_wd_2_0).val.arg).wd.2 _ _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (((_equal_wd_2_0).val.arg).val.left).wd.1 (((_equal_wd_2_0).val.arg).val.left).wd.2.1 (((_equal_wd_2_0).val.arg).val.left).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (((_equal_wd_2_0).val.arg).val.right).wd.1 (((_equal_wd_2_0).val.arg).val.right).wd.2.1 (((_equal_wd_2_0).val.arg).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))))).trans (congrArg M.number (by norm_num : (((1 : ℂ) / (2 : ℂ)) + ((1 : ℂ) / (2 : ℂ))) = (((1 : ℝ) : ℝ) : ℂ))))).trans (congrArg M.number (by have _value : Int.ceil (1 : ℝ) = (1 : ℤ) := Int.ceil_eq_iff.mpr ⟨by norm_num, by norm_num⟩; change ((Int.ceil (1 : ℝ) : ℤ) : ℂ) = (1 : ℂ); rw [_value]; norm_num))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
          exact ((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))) = ((Litex.roundingValue (M := M) true) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i5 (M := M));
          let _object_w17 := (_equal_wd_1_0).val.argument;
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _wd_1_0 _object_w17 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w17
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w17).wd.1 (_object_w17).wd.2.1 (_object_w17).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_339 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (Litex.roundingValue (M := M) true (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i6))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i6 : M.Value) => (Litex.roundingValue (M := M) true (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i6))) (Litex.denote _litex_literal.val.argument) = ((Litex.roundingValue (M := M) true) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))) from rfl))
        ))).trans (congrArg (Litex.roundingValue (M := M) true) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))) = (M.addValue (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))) from by
          let _litex_original := (let _object_w18 := (_equal_wd_1_0).val.argument;
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w18 (h_145 (M := M)) (by
            let _atomic_wd_1_0 := _object_w18
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w18).wd.1 (_object_w18).wd.2.1 (_object_w18).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro))
          let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
          let _object_w19 := (_equal_wd_1_0).val.argument;
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _wd_1_0 _object_w19 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w19
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w19).wd.1 (_object_w19).wd.2.1 (_object_w19).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_146 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))) from rfl))
        )))).trans _litex_residual)))
      )
  )

noncomputable def _object_w33 := (let _object_w22 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (_object_i5 (M := M)) _object_w22 (h_338 (M := M)) (by
  let _atomic_wd_1_0 := _object_w22
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w22).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) True.intro))

noncomputable def _object_w34 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))

theorem h_662 : (by
  let _equal_wd_1_0 := (_object_w33 (M := M))
  let _equal_wd_1_1 := (_object_w34 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w33 (M := M));
        let _equal_wd_1_1 := (_object_w34 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (M.negValue (M.number (2 : ℂ)))) = (M.negValue (M.number (1 : ℂ))) from by
          have _litex_residual : ((Litex.roundingValue (M := M) true) (M.addValue (M.negValue (M.number (2 : ℂ))) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))) = (M.negValue (M.number (1 : ℂ))) := (let _equal_wd_2_0 := (let _wd_1_0 := (let _wd_2_0 := (_equal_wd_1_0).val.argument;
          let _wd_2_1 := ((_object_w20 (M := M))).val.argument;
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = (-2 : ℂ)))) (Litex.numberInC (M := M) (-2 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (2 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (2 : ℂ)) = ((1 : ℂ) / (2 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (2 : ℂ)))))));
          (Litex.ceil _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((- (2 : ℂ)) + ((1 : ℂ) / (2 : ℂ))) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_1_0).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_atomic_wd_1_0).val.right).wd.1 ((_atomic_wd_1_0).val.right).wd.2.1 ((_atomic_wd_1_0).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (Litex.NativeBridge.numberInROfEq ((- (2 : ℂ)) + ((1 : ℂ) / (2 : ℂ))) ((-3 : ℝ) / (2 : ℝ)) (by norm_num))))));
          let _equal_wd_2_1 := _equal_wd_1_1;
          (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 _equal_wd_2_1 (-1 : ℂ) (- (1 : ℂ)) (let _round := _equal_wd_2_0;
          let _member : Litex.In _round Litex.C := Litex.integerToComplex _round (Litex.roundingInZ _round);
          (Litex.roundingDenoteReal _round ((-3 : ℝ) / (2 : ℝ)) (((Litex.NativeBridge.denoteAdd ((_equal_wd_2_0).val.arg).val.left ((_equal_wd_2_0).val.arg).val.right ((_equal_wd_2_0).val.arg).wd.1 ((_equal_wd_2_0).val.arg).wd.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (((_equal_wd_2_0).val.arg).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (((_equal_wd_2_0).val.arg).val.right).wd.1 (((_equal_wd_2_0).val.arg).val.right).wd.2.1 (((_equal_wd_2_0).val.arg).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (2 : ℂ)) + ((1 : ℂ) / (2 : ℂ))) = ((((-3 : ℝ) / (2 : ℝ)) : ℝ) : ℂ))))).trans (congrArg M.number (by have _value : Int.ceil ((-3 : ℝ) / (2 : ℝ)) = (-1 : ℤ) := Int.ceil_eq_iff.mpr ⟨by norm_num, by norm_num⟩; change ((Int.ceil ((-3 : ℝ) / (2 : ℝ)) : ℤ) : ℂ) = (-1 : ℂ); rw [_value]; norm_num))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by norm_num))))
          exact ((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (M.negValue (M.number (2 : ℂ)))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (M.negValue (M.number (2 : ℂ)))) = ((Litex.roundingValue (M := M) true) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.negValue (M.number (2 : ℂ))))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i5 (M := M));
          let _object_w30 := (_equal_wd_1_0).val.argument;
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _wd_1_0 _object_w30 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w30
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w30).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_339 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (Litex.roundingValue (M := M) true (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i6))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i6 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i6 : M.Value) => (Litex.roundingValue (M := M) true (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) _raw_i6))) (Litex.denote _litex_literal.val.argument) = ((Litex.roundingValue (M := M) true) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.negValue (M.number (2 : ℂ))))) from rfl))
        ))).trans (congrArg (Litex.roundingValue (M := M) true) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.negValue (M.number (2 : ℂ)))) = (M.addValue (M.negValue (M.number (2 : ℂ))) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))) from by
          let _litex_original := (let _object_w31 := (_equal_wd_1_0).val.argument;
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w31 (h_145 (M := M)) (by
            let _atomic_wd_1_0 := _object_w31
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w31).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) True.intro))
          let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
          let _object_w32 := (_equal_wd_1_0).val.argument;
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _wd_1_0 _object_w32 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w32
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w32).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_146 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.negValue (M.number (2 : ℂ))) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))) from rfl))
        )))).trans _litex_residual)))
      )
  )

theorem h_1137 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_1140 : Litex.In _value_i7 (Litex.Z (M := M))), (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i7 (h_32 (M := M)) (Litex.integerToReal _value_i7 h_1140) True.intro)
  exact Litex.Same _equal_wd_1_0 _value_i7) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_1140
          have h_1164 : Litex.In _value_i7 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_1140
                )
            )
          let _object_w37 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i7 (h_32 (M := M)) (Litex.integerToReal _value_i7 h_1164) True.intro)

          let _object_w38 := (Litex.floor _value_i7 (Litex.integerToReal _value_i7 h_1164))

          have h_1138 : (by
            let _equal_wd_1_0 := _object_w37
            let _equal_wd_1_1 := _object_w38
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w37;
                  let _equal_wd_1_1 := _object_w38;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i7)) = ((Litex.roundingValue (M := M) false) (Litex.denote _value_i7)) from by
                    have _litex_residual : ((Litex.roundingValue (M := M) false) (Litex.denote _value_i7)) = ((Litex.roundingValue (M := M) false) (Litex.denote _value_i7)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i7)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i7)) = ((Litex.roundingValue (M := M) false) (Litex.denote _value_i7)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := _value_i7;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.integerToReal _wd_1_1 h_1164) True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_33 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.roundingValue (M := M) false _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (Litex.roundingValue (M := M) false _raw_i2)) (Litex.denote _litex_literal.val.argument) = ((Litex.roundingValue (M := M) false) (Litex.denote _value_i7)) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          have h_1139 : (by
            let _equal_wd_1_0 := _object_w38
            exact Litex.Same _equal_wd_1_0 _value_i7) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w38;
                  (show Litex.Same _equal_wd_1_0 _value_i7 from (by
                    let _round := _equal_wd_1_0
                    exact (Litex.roundingOfInteger _round h_1164)
                  )))
                )
            )
          exact ((h_1138).trans h_1139)
        )
      )
  )

theorem h_1395 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_32 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_1396 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))
                )
            )
          have h_1397 : Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_32 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro) (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_1137 (M := M)) (Litex.number (M := M) (3 : ℂ)) h_1396)
                )
            )
          exact (let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_32 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro);
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_1397).trans (Litex.sameRefl (Litex.number (M := M) (3 : ℂ)))))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_shifted_x5f_rounding_x5f_function_x2f_statement_x2e_lit
