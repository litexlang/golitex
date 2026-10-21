import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_composed_x5f_real_x5f_formula_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_14) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_14) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInR _value_i2 (Litex.number (M := M) (1 : ℂ)) h_14 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))))
theorem h_53 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i1 (M := M)))
theorem h_54 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (Litex.sameRefl (_object_i1 (M := M)))

noncomputable def _object_i3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by
  intro _raw_i4 _raw_i5 h_68 h_69 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_68)
  have h_68 : Litex.In _value_i4 (Litex.R (M := M)) := h_68
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_69)
  have h_69 : Litex.In _value_i5 (Litex.R (M := M)) := h_69
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i4 _value_i5 (M.real_subset_complex _ h_68) (M.real_subset_complex _ h_69))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i4 _value_i5 (M.real_subset_complex _ h_68) (M.real_subset_complex _ h_69))
    exact (Litex.addInR _value_i4 _value_i5 h_68 h_69))))
theorem h_159 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i3 (M := M)))
theorem h_160 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (Litex.sameRefl (_object_i3 (M := M)))

noncomputable def _object_i6 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7)]))) (by
  intro _raw_i7 h_174 _
  let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_174)
  have h_174 : Litex.In _value_i7 (Litex.R (M := M)) := h_174
  change (by
    let _atomic_wd_1_0 := (let _object_w11 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i7 (h_53 (M := M)) h_174 True.intro);
    let _wd_1_1 := _object_w11;
    (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) _object_w11 _wd_1_1 (h_159 (M := M)) (by
      let _litex_return_call := _object_w11
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)) (by
      let _litex_return_call := _object_w11
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)) True.intro))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _object_w11 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i7 (h_53 (M := M)) h_174 True.intro);
    let _wd_1_1 := _object_w11;
    (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) _object_w11 _wd_1_1 (h_159 (M := M)) (by
      let _litex_return_call := _object_w11
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)) (by
      let _litex_return_call := _object_w11
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)) True.intro))
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call)))))
theorem h_541 : Litex.In (_object_i6 (M := M)) (Litex.fnSet ((_object_i6 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i6 (M := M)))
theorem h_542 : Litex.Same (_object_i6 (M := M)) (_object_i6 (M := M)) :=
  (Litex.sameRefl (_object_i6 (M := M)))

noncomputable def _object_w17 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => True) (_object_i6 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_541 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)

theorem h_543 : Litex.Same (_object_w17 (M := M)) (Litex.number (M := M) (6 : ℂ)) :=
  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i6 (M := M))) (M.number (2 : ℂ))) = (M.number (6 : ℂ)) from by
    have _litex_residual : (M.addValue (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ)))) = (M.number (6 : ℂ)) := (Litex.NativeBridge.sameOfDenoteNumber (let _wd_1_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
    let _wd_1_1 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.add _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) + (1 : ℂ)) = (3 : ℂ)))) (Litex.numberInC (M := M) (3 : ℂ)))) (by
      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) + (1 : ℂ)) = (3 : ℂ)))) (Litex.numberInC (M := M) (3 : ℂ)))))) (Litex.number (M := M) (6 : ℂ)) (((2 : ℂ) + (1 : ℂ)) + ((2 : ℂ) + (1 : ℂ))) (6 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (by
      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) + (1 : ℂ)) = (3 : ℂ)))) (Litex.numberInC (M := M) (3 : ℂ)))) (by
      let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((2 : ℂ) + (1 : ℂ)) = (3 : ℂ)))) (Litex.numberInC (M := M) (3 : ℂ)))) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (by norm_num))
    exact ((((((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i6 (M := M))) (M.number (2 : ℂ))))).trans (by
    let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => True) (_object_i6 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_541 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)
    let _litex_literal := (let _wd_1_0 := (_object_i6 (M := M));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_542 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7)]))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i7 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) _raw_i7)]))) (Litex.denote _litex_literal.val.argument) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ)))])) from rfl))
  ))).trans (congrArg (fun _x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_x, (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ)))])) (by
    let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)
    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_54 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) from rfl))
  )))).trans (congrArg (fun _x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))), _x])) (by
    let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)
    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_54 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) from rfl))
  )))).trans (by
    let _litex_original := (let _object_w15 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
    let _wd_1_1 := _object_w15;
    (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) _object_w15 _wd_1_1 (h_159 (M := M)) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((2 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_object_w15).wd.1 (_object_w15).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (1 : ℂ)) (3 : ℝ) (by norm_num))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((2 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_object_w15).wd.1 (_object_w15).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (1 : ℂ)) (3 : ℝ) (by norm_num))) True.intro))
    let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
    let _object_w16 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
    let _wd_1_2 := _object_w16;
    (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _wd_1_0 _object_w16 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.inOfDenoteNumber _wd_1_2 ((2 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_object_w16).wd.1 (_object_w16).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (1 : ℂ)) (3 : ℝ) (by norm_num))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_2 ((2 : ℂ) + (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_object_w16).wd.1 (_object_w16).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((2 : ℂ) + (1 : ℂ)) (3 : ℝ) (by norm_num))) True.intro))
    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_160 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.real) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.addValue _raw_i4 _raw_i5)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.addValue (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ)))) from rfl))
  ))).trans _litex_residual)
end LitexCompiled.file_lean_x2f_examples_x2f_composed_x5f_real_x5f_formula_x2f_statement_x2e_lit
