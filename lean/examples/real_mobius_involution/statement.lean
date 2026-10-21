import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_mobius_x5f_involution_x2f_statement_x2e_lit

universe u v1 v5 v6 v8
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.R (M := M))) (h_1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ))), (by
  let _object_w3 := (Litex.sub _value_i1 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_16) (Litex.numberInC (M := M) (1 : ℂ)))
  exact (by
    let _atomic_wd_1_0 := _object_w3
    exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))
) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_16 h_1
    let _object_w3 := (Litex.sub _value_i1 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_16) (Litex.numberInC (M := M) (1 : ℂ)))
    have h_2 : (by
      let _atomic_wd_1_0 := _object_w3
      exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
      (by
        let _atomic_wd_1_0 := _object_w3
        exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i1 h_16) (Litex.numberInC (M := M) (1 : ℂ)) h_1) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
    exact h_2
  )

noncomputable def _object_i2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (fun (_raw_i3 : M.Value) => (M.divValue (M.addValue _raw_i3 (M.number (1 : ℂ))) (M.subValue _raw_i3 (M.number (1 : ℂ))))) (by
  intro _raw_i3 h_94 h_55
  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_94)
  have h_94 : Litex.In _value_i3 (Litex.R (M := M)) := h_94
  have h_55 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
    (by
      change (¬ (_raw_i3 = (M.number (1 : ℂ))))
      exact h_55)
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_94) (Litex.numberInC (M := M) (1 : ℂ)));
    let _wd_1_1 := (Litex.sub _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_94) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_94) (Litex.numberInC (M := M) (1 : ℂ)))
      exact (Litex.addInC _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_94) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_2_0 := (Litex.sub _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_94) (Litex.numberInC (M := M) (1 : ℂ)))
      exact (Litex.subInC _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_94) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_2_0 := (Litex.sub _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_94) (Litex.numberInC (M := M) (1 : ℂ)))
      exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i3 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i3 h_94) (Litex.numberInC (M := M) (1 : ℂ)) h_55) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_94) (Litex.numberInC (M := M) (1 : ℂ)));
    let _wd_1_1 := (Litex.sub _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_94) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_94) (Litex.numberInC (M := M) (1 : ℂ)))
      exact (Litex.addInC _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_94) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_2_0 := (Litex.sub _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_94) (Litex.numberInC (M := M) (1 : ℂ)))
      exact (Litex.subInC _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_94) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_2_0 := (Litex.sub _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_94) (Litex.numberInC (M := M) (1 : ℂ)))
      exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i3 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i3 h_94) (Litex.numberInC (M := M) (1 : ℂ)) h_55) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))
    exact (Litex.divInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.addInR _value_i3 (Litex.number (M := M) (1 : ℂ)) h_94 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))) (Litex.subInR _value_i3 (Litex.number (M := M) (1 : ℂ)) h_94 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))) (_atomic_wd_1_0).wd.2.2))))
theorem h_352 : Litex.In (_object_i2 (M := M)) (Litex.fnSet ((_object_i2 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i2 (M := M)))
theorem h_353 : Litex.Same (_object_i2 (M := M)) (_object_i2 (M := M)) :=
  (Litex.sameRefl (_object_i2 (M := M)))

theorem h_356 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_370 : Litex.In _value_i5 (Litex.R (M := M))) (h_354 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w14 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _value_i5 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_370) h_354)
  exact (by
    let _atomic_wd_1_0 := _object_w14
    exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))
) :=
  (by
    intro _Host_i5 _rep_i5 _value_i5 h_370 h_354
    let _object_w14 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _value_i5 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_370) h_354)
    have h_355 : (by
      let _atomic_wd_1_0 := _object_w14
      exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
      (by
        let _atomic_wd_1_0 := _object_w14
        exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (2 : ℂ)) _value_i5 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.realToComplex _value_i5 h_370) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_354) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
    exact h_355
  )

theorem h_424 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_428 : Litex.In _value_i6 (Litex.R (M := M))) (h_422 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (1 : ℂ))), ¬ Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (_object_i2 (M := M)) _value_i6 (h_352 (M := M)) h_428 h_422) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    intro _Host_i6 _rep_i6 _value_i6 h_428 h_422
    have h_440 : Litex.In _value_i6 (Litex.R (M := M)) :=
      h_428
    let _object_w19 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (_object_i2 (M := M)) _value_i6 (h_352 (M := M)) h_440 h_422)

    let _object_w20 := (let _wd_1_0 := (Litex.add _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)));
    let _wd_1_1 := (Litex.sub _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := (Litex.add _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)))
      exact (Litex.addInC _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_1_0 := (Litex.sub _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)))
      exact (Litex.subInC _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_1_0 := (Litex.sub _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)))
      exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_440) (Litex.numberInC (M := M) (1 : ℂ)) h_422) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))

    have h_425 : Litex.Same _object_w19 _object_w20 :=
      (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i6)) = (M.divValue (M.addValue (Litex.denote _value_i6) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i6) (M.number (1 : ℂ)))) from by
        have _litex_residual : (M.divValue (M.addValue (Litex.denote _value_i6) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i6) (M.number (1 : ℂ)))) = (M.divValue (M.addValue (Litex.denote _value_i6) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i6) (M.number (1 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i6)))).trans (by
        let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (_object_i2 (M := M)) _value_i6 (h_352 (M := M)) h_440 h_422)
        let _litex_literal := (let _wd_1_0 := (_object_i2 (M := M));
        let _wd_1_1 := _value_i6;
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_440 h_422))
        have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_353 (M := M)) (Litex.sameRefl _litex_original.val.argument)
        have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (fun (_raw_i3 : M.Value) => (M.divValue (M.addValue _raw_i3 (M.number (1 : ℂ))) (M.subValue _raw_i3 (M.number (1 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
        exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i3 : M.Value) => (M.divValue (M.addValue _raw_i3 (M.number (1 : ℂ))) (M.subValue _raw_i3 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (Litex.denote _value_i6) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i6) (M.number (1 : ℂ)))) from rfl))
      ))).trans _litex_residual)
    let _object_w21 := (let _wd_1_0 := _object_w19;
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.sub _wd_1_0 _wd_1_1 (Litex.realToComplex _object_w19 (Litex.callInOutput _object_w19)) (Litex.numberInC (M := M) (1 : ℂ))))

    let _object_w22 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
    let _wd_1_1 := (Litex.sub _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
      let _atomic_wd_1_0 := (Litex.sub _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)))
      exact (Litex.subInC _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_1_0 := (Litex.sub _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)))
      exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_440) (Litex.numberInC (M := M) (1 : ℂ)) h_422) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))

    have h_426 : Litex.Same _object_w21 _object_w22 :=
      (((congrArg₂ M.subValue (by
        let _litex_original := _object_w19
        let _litex_literal := (let _wd_1_0 := (_object_i2 (M := M));
        let _wd_1_1 := _value_i6;
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_440 h_422))
        have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_353 (M := M)) (Litex.sameRefl _litex_original.val.argument)
        have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (fun (_raw_i3 : M.Value) => (M.divValue (M.addValue _raw_i3 (M.number (1 : ℂ))) (M.subValue _raw_i3 (M.number (1 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
        exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i3 : M.Value) => (M.divValue (M.addValue _raw_i3 (M.number (1 : ℂ))) (M.subValue _raw_i3 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (Litex.denote _value_i6) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i6) (M.number (1 : ℂ)))) from rfl))
      ) (Eq.refl (M.number (1 : ℂ))))).trans (((Litex.NativeBridge.sameOfDenoteNumber _ _ ((((Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_440)) + (1 : ℂ)) / ((Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_440)) - (1 : ℂ))) - (1 : ℂ)) ((2 : ℂ) / ((Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_440)) - (1 : ℂ))) (Litex.NativeBridge.denoteSub _object_w20 (Litex.number (M := M) (1 : ℂ)) (Litex.divInC (_object_w20).val.left (_object_w22).val.right (Litex.addInC _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ))) (_object_w20).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteDiv (_object_w20).val.left (_object_w20).val.right (_object_w20).wd.1 (_object_w20).wd.2.1 (_object_w20).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd _value_i6 (Litex.number (M := M) (1 : ℂ)) ((_object_w20).val.left).wd.1 ((_object_w20).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.realToComplex _value_i6 h_440)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteSub _value_i6 (Litex.number (M := M) (1 : ℂ)) ((_object_w20).val.right).wd.1 ((_object_w20).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.realToComplex _value_i6 h_440)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) (Litex.sub _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.numberInC (M := M) (2 : ℂ)) (by
        let _atomic_wd_1_0 := (Litex.sub _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)))
        exact (Litex.subInC _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)))) (by
        let _atomic_wd_1_0 := (Litex.sub _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)))
        exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_440) (Litex.numberInC (M := M) (1 : ℂ)) h_422) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ))))))) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteSub _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.realToComplex _value_i6 h_440)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (by
        have _litex_nz_0 : (((Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_440)) - (1 : ℂ)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (_object_w22).val.right ((Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_440)) - (1 : ℂ)) (Litex.NativeBridge.denoteSub _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.realToComplex _value_i6 h_440)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by
        let _atomic_wd_1_0 := (Litex.sub _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)))
        exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_440) (Litex.numberInC (M := M) (1 : ℂ)) h_422) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
        litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
      ))).trans ((Eq.refl (M.divValue (M.number (2 : ℂ)) (M.subValue (Litex.denote _value_i6) (M.number (1 : ℂ)))))).symm))
    have h_427 : ¬ Litex.Same _object_w22 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        have h_3477 : (by
          let _atomic_wd_2_0 := (Litex.sub _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)))
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M))) :=
          (by
            let _atomic_wd_2_0 := (Litex.sub _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)))
            exact (Litex.subInR _value_i6 (Litex.number (M := M) (1 : ℂ)) h_440 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))
        have h_3511 : (by
          let _atomic_wd_2_0 := (Litex.sub _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)))
          exact ¬ Litex.Same _atomic_wd_2_0 (Litex.number (M := M) (0 : ℂ))) :=
          (by
            let _atomic_wd_2_0 := (Litex.sub _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)))
            exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_440) (Litex.numberInC (M := M) (1 : ℂ)) h_422) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
        exact (Litex.notSameOfSame _object_w22 _object_w22 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (congrArg₂ M.divValue (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) (Litex.sameRefl (_object_w22).val.right)) (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) ((h_356 (M := M)) (_object_w22).val.right h_3477 h_3511))
      )
    exact (Litex.notSameOfSubNonzero (_object_w21).val.left (Litex.number (M := M) (1 : ℂ)) (let _litex_numeric_call := _object_w19;
    let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
    _litex_numeric_member) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.notSameOfSame _object_w22 _object_w21 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_426).symm (show @Eq M.Value _ _ from Eq.refl _) h_427))
  )

theorem h_3588 : ∀ {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_3594 : Litex.In _value_i8 (Litex.R (M := M))) (h_3586 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (1 : ℂ))), Litex.Same (let _object_w28 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (_object_i2 (M := M)) _value_i8 (h_352 (M := M)) h_3594 h_3586);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (_object_i2 (M := M)) _object_w28 (h_352 (M := M)) (by
  let _litex_return_call := _object_w28
  exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)) (by
  have h_3681 : Litex.In _value_i8 (Litex.R (M := M)) :=
    h_3594
  have h_3686 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (1 : ℂ)) :=
    h_3586
  exact (Litex.notSameOfSame _object_w28 _object_w28 (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i2 (M := M))) (Litex.sameRefl _value_i8)) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) ((h_424 (M := M)) _value_i8 h_3681 h_3686))
))) _value_i8 :=
  (by
    intro _Host_i8 _rep_i8 _value_i8 h_3594 h_3586
    have h_3691 : Litex.In _value_i8 (Litex.R (M := M)) :=
      h_3594
    let _object_w31 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (_object_i2 (M := M)) _value_i8 (h_352 (M := M)) h_3691 h_3586)

    have h_3589 : (by
      let _atomic_wd_1_0 := _object_w31
      exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
      (by
        let _atomic_wd_1_0 := _object_w31
        exact (by
          have h_3724 : Litex.In _value_i8 (Litex.R (M := M)) :=
            h_3691
          have h_3729 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (1 : ℂ)) :=
            h_3586
          exact (Litex.notSameOfSame _atomic_wd_1_0 _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i2 (M := M))) (Litex.sameRefl _value_i8)) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) ((h_424 (M := M)) _value_i8 h_3724 h_3729))
        ))
    let _object_w32 := (let _wd_1_0 := _object_w31;
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.sub _wd_1_0 _wd_1_1 (Litex.realToComplex _object_w31 (Litex.callInOutput _object_w31)) (Litex.numberInC (M := M) (1 : ℂ))))

    have h_3590 : (by
      let _atomic_wd_1_0 := _object_w32
      exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
      (by
        let _atomic_wd_1_0 := _object_w32
        exact (fun _litex_equal => (Litex.subNonzeroOfNotSame (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (let _litex_numeric_call := _object_w31;
        let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
        _litex_numeric_member) (Litex.numberInC (M := M) (1 : ℂ)) h_3589) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
    let _object_w34 := (let _wd_1_0 := (Litex.add _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ)));
    let _wd_1_1 := (Litex.sub _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ)));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := (Litex.add _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ)))
      exact (Litex.addInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_1_0 := (Litex.sub _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ)))
      exact (Litex.subInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ)))) (by
      let _atomic_wd_1_0 := (Litex.sub _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ)))
      exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i8 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 h_3691) (Litex.numberInC (M := M) (1 : ℂ)) h_3586) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))

    have h_3591 : Litex.Same _object_w31 _object_w34 :=
      (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) = (M.divValue (M.addValue (Litex.denote _value_i8) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i8) (M.number (1 : ℂ)))) from by
        have _litex_residual : (M.divValue (M.addValue (Litex.denote _value_i8) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i8) (M.number (1 : ℂ)))) = (M.divValue (M.addValue (Litex.denote _value_i8) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i8) (M.number (1 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)))).trans (by
        let _litex_original := _object_w31
        let _litex_literal := (let _wd_1_0 := (_object_i2 (M := M));
        let _wd_1_1 := _value_i8;
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_3691 h_3586))
        have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_353 (M := M)) (Litex.sameRefl _litex_original.val.argument)
        have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (fun (_raw_i3 : M.Value) => (M.divValue (M.addValue _raw_i3 (M.number (1 : ℂ))) (M.subValue _raw_i3 (M.number (1 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
        exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i3 : M.Value) => (M.divValue (M.addValue _raw_i3 (M.number (1 : ℂ))) (M.subValue _raw_i3 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (Litex.denote _value_i8) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i8) (M.number (1 : ℂ)))) from rfl))
      ))).trans _litex_residual)
    let _object_w35 := (let _wd_1_0 := _object_w34;
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.sub _wd_1_0 _wd_1_1 (Litex.divInC (_object_w34).val.left (_object_w34).val.right (Litex.addInC _value_i8 _wd_1_1 (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i8 _wd_1_1 (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) (_wd_1_0).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ))))

    have h_3592 : (by
      let _atomic_wd_1_0 := _object_w35
      exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
      (by
        let _atomic_wd_1_0 := _object_w35
        exact (fun _litex_equal => (Litex.subNonzeroOfNotSame (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.divInC (_object_w34).val.left (_object_w34).val.right (_object_w34).wd.1 (_object_w34).wd.2.1 (_object_w34).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.notSameOfSame (_object_w32).val.left (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) h_3591 (show @Eq M.Value _ _ from Eq.refl _) h_3589)) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
    have h_3593 : (Litex.Same (let _wd_1_0 := _object_w31;
    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (_object_i2 (M := M)) _wd_1_0 (h_352 (M := M)) (by
      let _litex_return_call := _object_w31
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)) h_3589)) (let _wd_1_0 := (let _wd_2_0 := _object_w31;
    let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.add _wd_2_0 _wd_2_1 (Litex.realToComplex _object_w31 (Litex.callInOutput _object_w31)) (Litex.numberInC (M := M) (1 : ℂ))));
    let _wd_1_1 := _object_w32;
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := (let _wd_2_0 := _object_w31;
      let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
      (Litex.add _wd_2_0 _wd_2_1 (Litex.realToComplex _object_w31 (Litex.callInOutput _object_w31)) (Litex.numberInC (M := M) (1 : ℂ))))
      exact (by
        let _arithmetic := _atomic_wd_1_0
        exact Litex.addInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (by
      let _arithmetic := _wd_1_1
      exact Litex.subInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2) h_3590))) ∧ ((Litex.Same (let _wd_1_0 := (let _wd_2_0 := _object_w31;
    let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.add _wd_2_0 _wd_2_1 (Litex.realToComplex _object_w31 (Litex.callInOutput _object_w31)) (Litex.numberInC (M := M) (1 : ℂ))));
    let _wd_1_1 := _object_w32;
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := (let _wd_2_0 := _object_w31;
      let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
      (Litex.add _wd_2_0 _wd_2_1 (Litex.realToComplex _object_w31 (Litex.callInOutput _object_w31)) (Litex.numberInC (M := M) (1 : ℂ))))
      exact (by
        let _arithmetic := _atomic_wd_1_0
        exact Litex.addInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2)) (by
      let _arithmetic := _wd_1_1
      exact Litex.subInC _arithmetic.val.left _arithmetic.val.right _arithmetic.wd.1 _arithmetic.wd.2) h_3590)) (let _wd_1_0 := (let _wd_2_0 := _object_w34;
    let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.add _wd_2_0 _wd_2_1 (Litex.divInC (_object_w34).val.left (_object_w34).val.right (Litex.addInC _value_i8 _wd_2_1 (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i8 _wd_2_1 (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) (_wd_2_0).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ))));
    let _wd_1_1 := _object_w35;
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := (let _wd_2_0 := _object_w34;
      let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
      (Litex.add _wd_2_0 _wd_2_1 (Litex.divInC (_object_w34).val.left (_object_w34).val.right (Litex.addInC _value_i8 _wd_2_1 (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i8 _wd_2_1 (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) (_wd_2_0).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ))))
      exact (Litex.addInC (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.divInC (_object_w34).val.left (_object_w34).val.right (Litex.addInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) ((_atomic_wd_1_0).val.left).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.subInC (_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.divInC (_object_w34).val.left (_object_w34).val.right (Litex.addInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) ((_wd_1_0).val.left).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ))) h_3592))) ∧ (Litex.Same (let _wd_1_0 := (let _wd_2_0 := _object_w34;
    let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
    (Litex.add _wd_2_0 _wd_2_1 (Litex.divInC (_object_w34).val.left (_object_w34).val.right (Litex.addInC _value_i8 _wd_2_1 (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i8 _wd_2_1 (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) (_wd_2_0).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ))));
    let _wd_1_1 := _object_w35;
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := (let _wd_2_0 := _object_w34;
      let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
      (Litex.add _wd_2_0 _wd_2_1 (Litex.divInC (_object_w34).val.left (_object_w34).val.right (Litex.addInC _value_i8 _wd_2_1 (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i8 _wd_2_1 (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) (_wd_2_0).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ))))
      exact (Litex.addInC (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.divInC (_object_w34).val.left (_object_w34).val.right (Litex.addInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) ((_atomic_wd_1_0).val.left).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.subInC (_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.divInC (_object_w34).val.left (_object_w34).val.right (Litex.addInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) ((_wd_1_0).val.left).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ))) h_3592)) _value_i8)) :=
      (And.intro (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8))) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) (M.number (1 : ℂ)))) from by
        have _litex_residual : (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) (M.number (1 : ℂ)))) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) (M.number (1 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8))))).trans (by
        let _litex_original := (let _wd_1_0 := _object_w31;
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (_object_i2 (M := M)) _wd_1_0 (h_352 (M := M)) (by
          let _litex_return_call := _object_w31
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)) h_3589))
        let _litex_literal := (let _wd_1_0 := (_object_i2 (M := M));
        let _wd_1_1 := _object_w31;
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (by
          let _litex_return_call := _object_w31
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)) h_3589))
        have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_353 (M := M)) (Litex.sameRefl _litex_original.val.argument)
        have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (fun (_raw_i3 : M.Value) => (M.divValue (M.addValue _raw_i3 (M.number (1 : ℂ))) (M.subValue _raw_i3 (M.number (1 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
        exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i3 : M.Value) => (M.divValue (M.addValue _raw_i3 (M.number (1 : ℂ))) (M.subValue _raw_i3 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) (M.number (1 : ℂ)))) from rfl))
      ))).trans _litex_residual) (And.intro (congrArg₂ M.divValue (congrArg₂ M.addValue h_3591 (show @Eq M.Value _ _ from Eq.refl _)) (congrArg₂ M.subValue h_3591 (show @Eq M.Value _ _ from Eq.refl _))) (Litex.NativeBridge.sameOfDenoteNumber _ _ (((((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3691)) + (1 : ℂ)) / ((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3691)) - (1 : ℂ))) + (1 : ℂ)) / ((((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3691)) + (1 : ℂ)) / ((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3691)) - (1 : ℂ))) - (1 : ℂ))) (Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3691)) (Litex.NativeBridge.denoteDiv (let _wd_1_0 := _object_w34;
      let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
      (Litex.add _wd_1_0 _wd_1_1 (Litex.divInC (_object_w34).val.left (_object_w34).val.right (Litex.addInC _value_i8 _wd_1_1 (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i8 _wd_1_1 (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) (_wd_1_0).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ)))) _object_w35 (by
        let _atomic_wd_1_0 := (let _wd_1_0 := _object_w34;
        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
        (Litex.add _wd_1_0 _wd_1_1 (Litex.divInC (_object_w34).val.left (_object_w34).val.right (Litex.addInC _value_i8 _wd_1_1 (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i8 _wd_1_1 (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) (_wd_1_0).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ))))
        exact (Litex.addInC (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.divInC (_object_w34).val.left (_object_w34).val.right (Litex.addInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) ((_atomic_wd_1_0).val.left).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ)))) (Litex.subInC (_object_w35).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.divInC (_object_w34).val.left (_object_w34).val.right (Litex.addInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) ((_object_w35).val.left).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ))) h_3592 _ _ (Litex.NativeBridge.denoteAdd _object_w34 (Litex.number (M := M) (1 : ℂ)) (Litex.divInC (_object_w34).val.left (_object_w34).val.right (Litex.addInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ))) ((_object_w35).val.left).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteDiv (_object_w34).val.left (_object_w34).val.right (_object_w34).wd.1 (_object_w34).wd.2.1 (_object_w34).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd _value_i8 (Litex.number (M := M) (1 : ℂ)) ((_object_w34).val.left).wd.1 ((_object_w34).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_3691)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteSub _value_i8 (Litex.number (M := M) (1 : ℂ)) ((_object_w34).val.right).wd.1 ((_object_w34).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_3691)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteSub (_object_w35).val.left (Litex.number (M := M) (1 : ℂ)) (_object_w35).wd.1 (_object_w35).wd.2 _ _ (Litex.NativeBridge.denoteDiv (_object_w34).val.left (_object_w34).val.right (_object_w34).wd.1 (_object_w34).wd.2.1 (_object_w34).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd _value_i8 (Litex.number (M := M) (1 : ℂ)) ((_object_w34).val.left).wd.1 ((_object_w34).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_3691)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteSub _value_i8 (Litex.number (M := M) (1 : ℂ)) ((_object_w34).val.right).wd.1 ((_object_w34).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_3691)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_3691)) (by
        have _litex_nz_0 : (((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3691)) - (1 : ℂ)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (_object_w34).val.right ((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3691)) - (1 : ℂ)) (Litex.NativeBridge.denoteSub _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_3691)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by
        let _atomic_wd_1_0 := (Litex.sub _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3691) (Litex.numberInC (M := M) (1 : ℂ)))
        exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i8 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 h_3691) (Litex.numberInC (M := M) (1 : ℂ)) h_3586) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
        have _litex_nz_1 : (((((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3691)) + (1 : ℂ)) / ((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3691)) - (1 : ℂ))) - (1 : ℂ)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _object_w35 ((((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3691)) + (1 : ℂ)) / ((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3691)) - (1 : ℂ))) - (1 : ℂ)) (Litex.NativeBridge.denoteSub (_object_w35).val.left (Litex.number (M := M) (1 : ℂ)) (_object_w35).wd.1 (_object_w35).wd.2 _ _ (Litex.NativeBridge.denoteDiv (_object_w34).val.left (_object_w34).val.right (_object_w34).wd.1 (_object_w34).wd.2.1 (_object_w34).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd _value_i8 (Litex.number (M := M) (1 : ℂ)) ((_object_w34).val.left).wd.1 ((_object_w34).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_3691)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteSub _value_i8 (Litex.number (M := M) (1 : ℂ)) ((_object_w34).val.right).wd.1 ((_object_w34).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_3691)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) h_3592
        litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | exact _litex_nz_1 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
      ))))

    have h_10724 :=
      (And.left h_3593)

    have h_10725 :=
      (And.left (And.right h_3593))

    have h_10726 :=
      (And.right (And.right h_3593))

    have h_10727 :=
      h_10724

    have h_10728 :=
      h_10725

    have h_10729 :=
      h_10726

    have h_10730 :=
      (Eq.trans h_10724 h_10725)

    have h_10731 :=
      (Eq.trans (Eq.trans h_10724 h_10725) h_10726)

    have h_10732 :=
      (Eq.trans h_10725 h_10726)
    exact h_10731
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_mobius_x5f_involution_x2f_statement_x2e_lit
