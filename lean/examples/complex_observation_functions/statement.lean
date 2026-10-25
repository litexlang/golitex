import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_observation_x5f_functions_x2f_statement_x2e_lit

universe u v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.complex Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.re : ℂ)) _raw_i2)) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.C (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (Litex.re _value_i2 h_14)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.re _value_i2 h_14)
    exact (Litex.reInR _atomic_wd_1_0))))
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

noncomputable def _object_w10 := (let _object_w5 := (let _wd_2_0 := (Litex.number (M := M) (3 : ℂ));
let _wd_2_1 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I));
(Litex.add _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (3 : ℂ)) (by
  let _atomic_wd_1_0 := _wd_2_1
  exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
(Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w5 (h_32 (M := M)) (by
  let _atomic_wd_1_0 := _object_w5
  exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_object_w5).val.right (_object_w5).wd.1 (_object_w5).wd.2)) True.intro))

theorem h_34 : (by
  let _equal_wd_1_0 := (_object_w10 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w10 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) = (M.number (3 : ℂ)) from by
          have _litex_residual : ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.re : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) = (M.number (3 : ℂ)) := (let _equal_wd_2_0 := (let _wd_1_0 := (_equal_wd_1_0).val.argument;
          (Litex.re _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (3 : ℂ) (((let _complex := _equal_wd_2_0; Litex.denoteRealPart _complex ((3 : ℂ) + ((4 : ℂ) * Complex.I)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) ((_equal_wd_2_0).val.arg).val.right ((_equal_wd_2_0).val.arg).wd.1 ((_equal_wd_2_0).val.arg).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (((_equal_wd_2_0).val.arg).val.right).wd.1 (((_equal_wd_2_0).val.arg).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) Complex.I))))).trans (congrArg M.number (by norm_num : ((((3 : ℂ) + ((4 : ℂ) * Complex.I))).re : ℂ) = (3 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) = ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.re : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
          let _object_w9 := (_equal_wd_1_0).val.argument;
          (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _object_w9 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w9
            exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_object_w9).val.right (_object_w9).wd.1 (_object_w9).wd.2)) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_33 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.complex Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.re : ℂ)) _raw_i2)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.complex Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.re : ℂ)) _raw_i2)) (Litex.denote _litex_literal.val.argument) = ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.re : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) from rfl))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_i3 := (Litex.formulaFn (M := M) Litex.StandardSetValue.complex Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) _raw_i4)) (by
  intro _raw_i4 h_204 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_204)
  have h_204 : Litex.In _value_i4 (Litex.C (M := M)) := h_204
  change (by
    let _atomic_wd_1_0 := (Litex.complexAbs _value_i4 h_204)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.complexAbs _value_i4 h_204)
    exact (Litex.complexAbsInR _atomic_wd_1_0))))
theorem h_226 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i3 (M := M)))
      )
  )
theorem h_227 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i3 (M := M)))
      )
  )

noncomputable def _object_w21 := (let _object_w16 := ((_object_w10 (M := M))).val.argument;
(Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _object_w16 (h_226 (M := M)) (by
  let _atomic_wd_1_0 := _object_w16
  exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_object_w16).val.right (_object_w16).wd.1 (_object_w16).wd.2)) True.intro))

theorem h_228 : (by
  let _equal_wd_1_0 := (_object_w21 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w21 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) = (M.number (5 : ℂ)) from by
          have _litex_residual : ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) = (M.number (5 : ℂ)) := (let _equal_wd_2_0 := (let _wd_1_0 := (_equal_wd_1_0).val.argument;
          (Litex.complexAbs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (5 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (5 : ℂ)) (5 : ℂ) (5 : ℂ) (((let _complex := _equal_wd_2_0; Litex.denoteComplexAbs _complex ((3 : ℂ) + ((4 : ℂ) * Complex.I)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) ((_equal_wd_2_0).val.arg).val.right ((_equal_wd_2_0).val.arg).wd.1 ((_equal_wd_2_0).val.arg).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (((_equal_wd_2_0).val.arg).val.right).wd.1 (((_equal_wd_2_0).val.arg).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) Complex.I))))).trans (congrArg M.number (by have _norm : ‖(((3 : ℂ) + ((4 : ℂ) * Complex.I)))‖ = (5 : ℝ) := (by rw [Complex.norm_def]; exact (Real.sqrt_eq_iff_eq_sq (Complex.normSq_nonneg _) (by norm_num)).mpr (by norm_num [Complex.normSq])); exact (congrArg (fun r : ℝ => (r : ℂ)) _norm).trans (by norm_num) : (‖(((3 : ℂ) + ((4 : ℂ) * Complex.I)))‖ : ℂ) = (5 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) = ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
          let _object_w20 := (_equal_wd_1_0).val.argument;
          (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _wd_1_0 _object_w20 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w20
            exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_object_w20).val.right (_object_w20).wd.1 (_object_w20).wd.2)) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_227 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.complex Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) _raw_i4)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.complex Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) _raw_i4)) (Litex.denote _litex_literal.val.argument) = ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) from rfl))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_i5 := (Litex.formulaFn (M := M) Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) _raw_i6)) (by
  intro _raw_i6 h_494 _
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_494)
  have h_494 : Litex.In _value_i6 (Litex.C (M := M)) := h_494
  change (by
    let _atomic_wd_1_0 := (Litex.conj _value_i6 h_494)
    exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.conj _value_i6 h_494)
    exact (Litex.conjInC _atomic_wd_1_0))))
theorem h_520 : Litex.In (_object_i5 (M := M)) (Litex.fnSet ((_object_i5 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i5 (M := M)))
      )
  )
theorem h_521 : Litex.Same (_object_i5 (M := M)) (_object_i5 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i5 (M := M)))
      )
  )

theorem h_523 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_536 : Litex.In _value_i7 (Litex.C (M := M))), (by
  let _object_w33 := (let _object_w28 := (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i6 : M.Value) => True) (_object_i5 (M := M)) _value_i7 (h_520 (M := M)) h_536 True.intro);
  (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i6 : M.Value) => True) (_object_i5 (M := M)) _object_w28 (h_520 (M := M)) (by
    let _atomic_wd_1_0 := _object_w28
    exact (by
      let _litex_return_call := _object_w28
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
  exact (by
    let _equal_wd_1_0 := _object_w33
    exact Litex.Same _equal_wd_1_0 _value_i7)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_536
          let _object_w33 := (let _object_w28 := (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i6 : M.Value) => True) (_object_i5 (M := M)) _value_i7 (h_520 (M := M)) h_536 True.intro);
          (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i6 : M.Value) => True) (_object_i5 (M := M)) _object_w28 (h_520 (M := M)) (by
            let _atomic_wd_1_0 := _object_w28
            exact (by
              let _litex_return_call := _object_w28
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callInOutput _litex_return_call))) True.intro))
          have h_522 : (by
            let _equal_wd_1_0 := _object_w33
            exact Litex.Same _equal_wd_1_0 _value_i7) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w33;
                  (show Litex.Same _equal_wd_1_0 _value_i7 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i7))) = (Litex.denote _value_i7) from by
                    have _litex_residual : ((Litex.complexUnaryValue (M := M) (fun z : ℂ => star z)) ((Litex.complexUnaryValue (M := M) (fun z : ℂ => star z)) (Litex.denote _value_i7))) = (Litex.denote _value_i7) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.conj _value_i7 h_536);
                    (Litex.conj _wd_1_0 (by
                      let _atomic_wd_1_0 := (Litex.conj _value_i7 h_536)
                      exact (Litex.conjInC _atomic_wd_1_0))));
                    (show Litex.Same _equal_wd_2_0 _value_i7 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 _value_i7 (star ((star ((Litex.NativeBridge.asComplex _value_i7 h_536))))) (Litex.NativeBridge.asComplex _value_i7 h_536) (let _complex := _equal_wd_2_0; Litex.denoteConjugate _complex (star ((Litex.NativeBridge.asComplex _value_i7 h_536))) (let _complex := (_equal_wd_2_0).val.arg; Litex.denoteConjugate _complex (Litex.NativeBridge.asComplex _value_i7 h_536) (Litex.NativeBridge.asComplex_spec _value_i7 h_536))) (Litex.NativeBridge.asComplex_spec _value_i7 h_536) (by simp only [star_star]))))
                    exact ((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i7))))).trans (congrArg (fun _x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) _x) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i7)) = ((Litex.complexUnaryValue (M := M) (fun z : ℂ => star z)) (Litex.denote _value_i7)) from by
                    let _litex_original := (_equal_wd_1_0).val.argument
                    let _litex_literal := (let _wd_1_0 := (_object_i5 (M := M));
                    let _wd_1_1 := _value_i7;
                    (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i6 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_536 True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_521 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) _raw_i6)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i6 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i6 : M.Value) => (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) _raw_i6)) (Litex.denote _litex_literal.val.argument) = ((Litex.complexUnaryValue (M := M) (fun z : ℂ => star z)) (Litex.denote _value_i7)) from rfl))
                  )))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) ((Litex.complexUnaryValue (M := M) (fun z : ℂ => star z)) (Litex.denote _value_i7))) = ((Litex.complexUnaryValue (M := M) (fun z : ℂ => star z)) ((Litex.complexUnaryValue (M := M) (fun z : ℂ => star z)) (Litex.denote _value_i7))) from by
                    let _litex_original := (let _object_w31 := (Litex.conj _value_i7 h_536);
                    (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i6 : M.Value) => True) (_object_i5 (M := M)) _object_w31 (h_520 (M := M)) (by
                      let _atomic_wd_1_0 := _object_w31
                      exact (Litex.conjInC _atomic_wd_1_0)) True.intro))
                    let _litex_literal := (let _wd_1_0 := (_object_i5 (M := M));
                    let _object_w32 := (Litex.conj _value_i7 h_536);
                    (Litex.call Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i6 : M.Value) => True) _wd_1_0 _object_w32 (Litex.formulaFnInFnSet _wd_1_0) (by
                      let _atomic_wd_1_0 := _object_w32
                      exact (Litex.conjInC _atomic_wd_1_0)) True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_521 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) _raw_i6)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.complex Litex.StandardSetValue.complex (fun (_raw_i6 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i6 : M.Value) => (Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) _raw_i6)) (Litex.denote _litex_literal.val.argument) = ((Litex.complexUnaryValue (M := M) (fun z : ℂ => star z)) ((Litex.complexUnaryValue (M := M) (fun z : ℂ => star z)) (Litex.denote _value_i7))) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          exact h_522
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_observation_x5f_functions_x2f_statement_x2e_lit
