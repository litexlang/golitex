import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_shift_x5f_function_x2f_statement_x2e_lit

universe u v3 v4 v5
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

noncomputable def _object_w5 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_53 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)

theorem h_55 : (by
  let _equal_wd_1_0 := (_object_w5 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (let _equal_wd_1_0 := (_object_w5 (M := M));
  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))) = (M.number (3 : ℂ)) from by
    have _litex_residual : (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) = (M.number (3 : ℂ)) := (let _equal_wd_2_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
    (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) ((2 : ℂ) + (1 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))))
    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (2 : ℂ))))).trans (by
    let _litex_original := _equal_wd_1_0
    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_54 (M := M)) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) from rfl))
  ))).trans _litex_residual)))

theorem h_90 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_103 : Litex.In _value_i3 (Litex.R (M := M))), (by
  let _object_w8 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_53 (M := M)) h_103 True.intro)
  let _object_w9 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_103) (Litex.numberInC (M := M) (1 : ℂ)))
  exact (by
    let _equal_wd_1_0 := _object_w8
    let _equal_wd_1_1 := _object_w9
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    intro _Host_i3 _rep_i3 _value_i3 h_103
    let _object_w8 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i3 (h_53 (M := M)) h_103 True.intro)
    let _object_w9 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_103) (Litex.numberInC (M := M) (1 : ℂ)))
    have h_89 : (by
      let _equal_wd_1_0 := _object_w8
      let _equal_wd_1_1 := _object_w9
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w8;
            let _equal_wd_1_1 := _object_w9;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3)) = (M.addValue (Litex.denote _value_i3) (M.number (1 : ℂ))) from by
              have _litex_residual : (M.addValue (Litex.denote _value_i3) (M.number (1 : ℂ))) = (M.addValue (Litex.denote _value_i3) (M.number (1 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3)))).trans (by
              let _litex_original := _equal_wd_1_0
              let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
              let _wd_1_1 := _value_i3;
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_103 True.intro))
              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_54 (M := M)) (Litex.sameRefl _litex_original.val.argument)
              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (Litex.denote _value_i3) (M.number (1 : ℂ))) from rfl))
            ))).trans _litex_residual)))
          )
      )
    exact h_89
  )

theorem h_214 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_218 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_219 : Litex.In _value_i5 (Litex.R (M := M))), (by
  let _equal_wd_1_0 := (let _object_w11 := (Litex.add _value_i4 _value_i5 (M.real_subset_complex _ h_218) (M.real_subset_complex _ h_219));
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w11 (h_53 (M := M)) (by
    let _atomic_wd_1_0 := _object_w11
    exact (Litex.addInR _value_i4 _value_i5 h_218 h_219)) True.intro))
  let _equal_wd_1_1 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i4 (h_53 (M := M)) h_218 True.intro);
  let _wd_1_1 := _value_i5;
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (M.real_subset_complex _ h_219)))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    intro _Host_i4 _rep_i4 _value_i4 h_218 _Host_i5 _rep_i5 _value_i5 h_219
    have h_377 : Litex.In _value_i4 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_218
          )
      )
    have h_378 : Litex.In _value_i5 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_219
          )
      )
    let _object_w20 := (let _object_w13 := (Litex.add _value_i4 _value_i5 (M.real_subset_complex _ h_377) (M.real_subset_complex _ h_378));
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w13 (h_53 (M := M)) (by
      let _atomic_wd_1_0 := _object_w13
      exact (Litex.addInR _value_i4 _value_i5 h_377 h_378)) True.intro))

    let _object_w21 := (let _wd_1_0 := (Litex.add _value_i4 _value_i5 (M.real_subset_complex _ h_377) (M.real_subset_complex _ h_378));
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.add _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.addInC _value_i4 _value_i5 (M.real_subset_complex _ h_377) (M.real_subset_complex _ h_378))) (Litex.numberInC (M := M) (1 : ℂ))))

    have h_215 : (by
      let _equal_wd_1_0 := _object_w20
      let _equal_wd_1_1 := _object_w21
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w20;
            let _equal_wd_1_1 := _object_w21;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5))) = (M.addValue (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (M.number (1 : ℂ))) from by
              have _litex_residual : (M.addValue (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (M.number (1 : ℂ))) = (M.addValue (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (M.number (1 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5))))).trans (by
              let _litex_original := _equal_wd_1_0
              let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
              let _object_w19 := (_equal_wd_1_1).val.left;
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _object_w19 (Litex.formulaFnInFnSet _wd_1_0) (by
                let _atomic_wd_1_0 := _object_w19
                exact (Litex.addInR _value_i4 _value_i5 h_377 h_378)) True.intro))
              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_54 (M := M)) (Litex.sameRefl _litex_original.val.argument)
              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.addValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (M.number (1 : ℂ))) from rfl))
            ))).trans _litex_residual)))
          )
      )
    let _object_w22 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i4 (h_53 (M := M)) h_377 True.intro)

    let _object_w23 := (Litex.add _value_i4 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_377) (Litex.numberInC (M := M) (1 : ℂ)))

    have h_216 : (by
      let _equal_wd_1_0 := _object_w22
      let _equal_wd_1_1 := _object_w23
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w22;
            let _equal_wd_1_1 := _object_w23;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)) = (M.addValue (Litex.denote _value_i4) (M.number (1 : ℂ))) from by
              have _litex_residual : (M.addValue (Litex.denote _value_i4) (M.number (1 : ℂ))) = (M.addValue (Litex.denote _value_i4) (M.number (1 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)))).trans (by
              let _litex_original := _equal_wd_1_0
              let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
              let _wd_1_1 := _value_i4;
              (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_377 True.intro))
              have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_54 (M := M)) (Litex.sameRefl _litex_original.val.argument)
              have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (Litex.denote _value_i4) (M.number (1 : ℂ))) from rfl))
            ))).trans _litex_residual)))
          )
      )
    let _object_w24 := (let _wd_1_0 := _object_w23;
    let _wd_1_1 := _value_i5;
    (Litex.add _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _object_w23
      exact (Litex.addInC _value_i4 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_377) (Litex.numberInC (M := M) (1 : ℂ)))) (M.real_subset_complex _ h_378)))

    have h_217 : (by
      let _equal_wd_1_0 := _object_w21
      let _equal_wd_1_1 := _object_w24
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w21;
            let _equal_wd_1_1 := _object_w24;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_377)) + (Litex.NativeBridge.asComplex _value_i5 (Litex.realToComplex _value_i5 h_378))) + (1 : ℂ)) (((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 h_377)) + (1 : ℂ)) + (Litex.NativeBridge.asComplex _value_i5 (Litex.realToComplex _value_i5 h_378))) (Litex.NativeBridge.denoteAdd (_object_w21).val.left (Litex.number (M := M) (1 : ℂ)) (_object_w21).wd.1 (_object_w21).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i4 _value_i5 ((_object_w21).val.left).wd.1 ((_object_w21).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 h_377)) (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.realToComplex _value_i5 h_378))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteAdd (_equal_wd_1_1).val.left _value_i5 (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i4 (Litex.number (M := M) (1 : ℂ)) (_object_w23).wd.1 (_object_w23).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 h_377)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.realToComplex _value_i5 h_378))) (by ring!))))
          )
      )
    exact (Eq.trans ((h_215).trans h_217) (Eq.trans (congrArg₂ M.addValue (show (M.addValue (Litex.denote _value_i4) (M.number (1 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)) from (h_216).symm) (show (Litex.denote _value_i5) = (Litex.denote _value_i5) from (show @Eq M.Value _ _ from Eq.refl _))) (show @Eq M.Value _ _ from Eq.refl _)))
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_shift_x5f_function_x2f_statement_x2e_lit
