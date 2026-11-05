import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_showcases_x2f_litex_x5f_to_x5f_lean_x5f_adapter_x2f_mobius_x2e_lit

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
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_16 h_1
          let _object_w3 := (Litex.sub _value_i1 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_16) (Litex.numberInC (M := M) (1 : ℂ)))
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w3
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i1 h_16) (Litex.numberInC (M := M) (1 : ℂ)) h_1) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          exact h_2
        )
      )
  )

noncomputable def _object_i2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (fun (_raw_i3 : M.Value) => (M.divValue (M.addValue _raw_i3 (M.number (1 : ℂ))) (M.subValue _raw_i3 (M.number (1 : ℂ))))) (by
  intro _raw_i3 h_94 h_55
  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_94)
  have h_94 : Litex.In _value_i3 (Litex.R (M := M)) := h_94
  have h_55 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i3 = (M.number (1 : ℂ))))
            exact h_55)
        )
    )
  let _object_local_1 := (let _wd_1_0 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_94) (Litex.numberInC (M := M) (1 : ℂ)));
  let _wd_1_1 := (Litex.sub _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_94) (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.div _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.addInC _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_94) (Litex.numberInC (M := M) (1 : ℂ)))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.subInC _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_94) (Litex.numberInC (M := M) (1 : ℂ)))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i3 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i3 h_94) (Litex.numberInC (M := M) (1 : ℂ)) h_55) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))
  change (by
    let _atomic_wd_1_0 := _object_local_1
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := _object_local_1
    exact (Litex.divInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.addInR _value_i3 (Litex.number (M := M) (1 : ℂ)) h_94 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (rfl))) (Litex.subInR _value_i3 (Litex.number (M := M) (1 : ℂ)) h_94 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (rfl))) (_atomic_wd_1_0).wd.2.2))))
theorem h_352 : Litex.In (_object_i2 (M := M)) (Litex.fnSet ((_object_i2 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i2 (M := M)))
      )
  )
theorem h_353 : Litex.Same (_object_i2 (M := M)) (_object_i2 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i2 (M := M)))
      )
  )

theorem h_356 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_370 : Litex.In _value_i5 (Litex.R (M := M))) (h_354 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w14 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _value_i5 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_370) h_354)
  exact (by
    let _atomic_wd_1_0 := _object_w14
    exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_370 h_354
          let _object_w14 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _value_i5 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_370) h_354)
          have h_355 : (by
            let _atomic_wd_1_0 := _object_w14
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w14
                    exact (fun _litex_equal => (Litex.divNonzero (Litex.number (M := M) (2 : ℂ)) _value_i5 (Litex.numberInC (M := M) (2 : ℂ)) (Litex.realToComplex _value_i5 h_370) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) h_354) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          exact h_355
        )
      )
  )

theorem h_424 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_428 : Litex.In _value_i6 (Litex.R (M := M))) (h_422 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (1 : ℂ))), (let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (_object_i2 (M := M)) _value_i6 (h_352 (M := M)) h_428 h_422);
¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_428 h_422
          have h_440 : Litex.In _value_i6 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_428
                )
            )
          let _object_w19 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (_object_i2 (M := M)) _value_i6 (h_352 (M := M)) h_440 h_422)

          let _object_w20 := (let _wd_1_0 := (Litex.add _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_1_1 := (Litex.sub _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.subInC _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_440) (Litex.numberInC (M := M) (1 : ℂ)) h_422) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))

          have h_425 : (let _equal_wd_1_0 := _object_w19;
          let _equal_wd_1_1 := _object_w20;
          Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w19;
                  let _equal_wd_1_1 := _object_w20;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i6)) = (M.divValue (M.addValue (Litex.denote _value_i6) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i6) (M.number (1 : ℂ)))) from by
                    have _litex_residual : (M.divValue (M.addValue (Litex.denote _value_i6) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i6) (M.number (1 : ℂ)))) = (M.divValue (M.addValue (Litex.denote _value_i6) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i6) (M.number (1 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i6)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i6)) = (M.divValue (M.addValue (Litex.denote _value_i6) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i6) (M.number (1 : ℂ)))) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i2 (M := M));
                    let _wd_1_1 := _value_i6;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_440 h_422))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_353 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (fun (_raw_i3 : M.Value) => (M.divValue (M.addValue _raw_i3 (M.number (1 : ℂ))) (M.subValue _raw_i3 (M.number (1 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i3 : M.Value) => (M.divValue (M.addValue _raw_i3 (M.number (1 : ℂ))) (M.subValue _raw_i3 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (Litex.denote _value_i6) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i6) (M.number (1 : ℂ)))) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w21 := (let _wd_1_0 := _object_w19;
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w19
            exact (Litex.realToComplex _object_w19 (Litex.callInOutput _object_w19))) (Litex.numberInC (M := M) (1 : ℂ))))

          let _object_w22 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_1 := (_object_w20).val.right;
          (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.subInC _value_i6 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_440) (Litex.numberInC (M := M) (1 : ℂ)) h_422) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))

          have h_426 : (let _equal_wd_1_0 := _object_w21;
          let _equal_wd_1_1 := _object_w22;
          Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w21;
                  let _equal_wd_1_1 := _object_w22;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((congrArg₂ M.subValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i6)) = (M.divValue (M.addValue (Litex.denote _value_i6) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i6) (M.number (1 : ℂ)))) from by
                    let _litex_original := _object_w19
                    let _litex_literal := (let _wd_1_0 := (_object_i2 (M := M));
                    let _wd_1_1 := _value_i6;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_440 h_422))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_353 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (fun (_raw_i3 : M.Value) => (M.divValue (M.addValue _raw_i3 (M.number (1 : ℂ))) (M.subValue _raw_i3 (M.number (1 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i3 : M.Value) => (M.divValue (M.addValue _raw_i3 (M.number (1 : ℂ))) (M.subValue _raw_i3 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (Litex.denote _value_i6) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i6) (M.number (1 : ℂ)))) from rfl))
                  ) (Eq.refl (M.number (1 : ℂ))))).trans (((let _equal_wd_2_0 := (let _wd_1_0 := _object_w20;
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (Litex.sub _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _object_w20
                    exact (Litex.divInC (_object_w20).val.left (_equal_wd_1_1).val.right (Litex.addInC _value_i6 _wd_1_1 (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i6 _wd_1_1 (M.real_subset_complex _ h_440) (Litex.numberInC (M := M) (1 : ℂ))) (_atomic_wd_1_0).wd.2.2)) (Litex.numberInC (M := M) (1 : ℂ))));
                  let _equal_wd_2_1 := _equal_wd_1_1;
                  (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((((Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_440)) + (1 : ℂ)) / ((Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_440)) - (1 : ℂ))) - (1 : ℂ)) ((2 : ℂ) / ((Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_440)) - (1 : ℂ))) (Litex.NativeBridge.denoteSub (_equal_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteDiv (_object_w20).val.left (_object_w20).val.right (_object_w20).wd.1 (_object_w20).wd.2.1 (_object_w20).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd _value_i6 (Litex.number (M := M) (1 : ℂ)) ((_object_w20).val.left).wd.1 ((_object_w20).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.realToComplex _value_i6 h_440)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteSub _value_i6 (Litex.number (M := M) (1 : ℂ)) ((_object_w20).val.right).wd.1 ((_object_w20).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.realToComplex _value_i6 h_440)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_1).val.right (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2.1 (_equal_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteSub _value_i6 (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_2_1).val.right).wd.1 ((_equal_wd_2_1).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.realToComplex _value_i6 h_440)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (by
                    have _litex_nz_0 : (((Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_440)) - (1 : ℂ)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (_equal_wd_2_1).val.right ((Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_440)) - (1 : ℂ)) (Litex.NativeBridge.denoteSub _value_i6 (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_2_1).val.right).wd.1 ((_equal_wd_2_1).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.realToComplex _value_i6 h_440)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by
                    let _atomic_wd_1_0 := (_equal_wd_2_1).val.right
                    exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_440) (Litex.numberInC (M := M) (1 : ℂ)) h_422) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                    litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                  ))))).trans ((Eq.refl (M.divValue (M.number (2 : ℂ)) (M.subValue (Litex.denote _value_i6) (M.number (1 : ℂ)))))).symm))))
                )
            )
          have h_427 : (by
            let _atomic_wd_1_0 := _object_w22
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w22
                    exact (by
                      have h_3704 : (by
                        let _atomic_wd_2_0 := (_object_w22).val.right
                        exact Litex.In _atomic_wd_2_0 (Litex.R (M := M))) :=
                        (by
                          let _atomic_wd_2_0 := (_object_w22).val.right
                          exact (Litex.subInR _value_i6 (Litex.number (M := M) (1 : ℂ)) h_440 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (rfl))))
                      let _known_argument_0 := (_object_w22).val.right
                      have h_3738 : (by
                        let _atomic_wd_2_0 := (_object_w22).val.right
                        exact ¬ Litex.Same _atomic_wd_2_0 (Litex.number (M := M) (0 : ℂ))) :=
                        (by
                          let _atomic_wd_2_0 := (_object_w22).val.right
                          exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i6 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_440) (Litex.numberInC (M := M) (1 : ℂ)) h_422) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                      exact (Eq.mp (congrArg₂ (fun (x y : M.Value) => x ≠ y) (congrArg₂ M.divValue (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) (by
                      let _matched := (_object_w22).val.right
                      exact Litex.sameRefl _matched)) (Litex.sameRefl (Litex.number (M := M) (0 : ℂ)))) ((h_356 (M := M)) (Litex.semanticObject (Litex.denote _known_argument_0) (Litex.isSet _known_argument_0)) h_3704 h_3738))
                    ))
                )
            )
          exact (by
            let _atomic_wd_1_0 := _object_w19
            exact (Litex.notSameOfSubNonzero _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (let _litex_numeric_call := _object_w19;
            let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
            _litex_numeric_member) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.notSameOfSame _object_w22 _object_w21 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (h_426).symm (show @Eq M.Value _ _ from Eq.refl _) h_427)))
        )
      )
  )

theorem h_3815 : ∀ {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_3821 : Litex.In _value_i8 (Litex.R (M := M))) (h_3813 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (1 : ℂ))), (let _equal_wd_1_0 := (let _object_w28 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (_object_i2 (M := M)) _value_i8 (h_352 (M := M)) h_3821 h_3813);
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (_object_i2 (M := M)) _object_w28 (h_352 (M := M)) (by
  let _atomic_wd_1_0 := _object_w28
  exact (by
    let _litex_return_call := _object_w28
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
  let _atomic_wd_1_0 := _object_w28
  exact (by
    have h_3908 : Litex.In _value_i8 (Litex.R (M := M)) :=
      h_3821
    let _known_argument_0 := _value_i8
    have h_3913 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (1 : ℂ)) :=
      h_3813
    exact (Eq.mp (congrArg₂ (fun (x y : M.Value) => x ≠ y) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i2 (M := M))) (by
    let _matched := _value_i8
    exact Litex.sameRefl _matched)) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))) ((h_424 (M := M)) (Litex.semanticObject (Litex.denote _known_argument_0) (Litex.isSet _known_argument_0)) h_3908 h_3913))
  ))));
Litex.Same _equal_wd_1_0 _value_i8) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i8 _rep_i8 _value_i8 h_3821 h_3813
          have h_3918 : Litex.In _value_i8 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_3821
                )
            )
          let _object_w31 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (_object_i2 (M := M)) _value_i8 (h_352 (M := M)) h_3918 h_3813)

          have h_3816 : (by
            let _atomic_wd_1_0 := _object_w31
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w31
                    exact (by
                      have h_3951 : Litex.In _value_i8 (Litex.R (M := M)) :=
                        h_3918
                      let _known_argument_0 := _value_i8
                      have h_3956 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (1 : ℂ)) :=
                        h_3813
                      exact (Eq.mp (congrArg₂ (fun (x y : M.Value) => x ≠ y) (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i2 (M := M))) (by
                      let _matched := _value_i8
                      exact Litex.sameRefl _matched)) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))) ((h_424 (M := M)) (Litex.semanticObject (Litex.denote _known_argument_0) (Litex.isSet _known_argument_0)) h_3951 h_3956))
                    ))
                )
            )
          let _object_w32 := (let _wd_1_0 := _object_w31;
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w31
            exact (Litex.realToComplex _object_w31 (Litex.callInOutput _object_w31))) (Litex.numberInC (M := M) (1 : ℂ))))

          have h_3817 : (by
            let _atomic_wd_1_0 := _object_w32
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w32
                    exact (fun _litex_equal => (Litex.subNonzeroOfNotSame (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (let _litex_numeric_call := _object_w31;
                    let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (show Litex.In _litex_numeric_call Litex.R from (Litex.callInOutput _litex_numeric_call)));
                    _litex_numeric_member) (Litex.numberInC (M := M) (1 : ℂ)) (by
                      let _atomic_wd_2_0 := _object_w31
                      exact h_3816)) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          let _object_w34 := (let _wd_1_0 := (Litex.add _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3918) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_1_1 := (Litex.sub _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3918) (Litex.numberInC (M := M) (1 : ℂ)));
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3918) (Litex.numberInC (M := M) (1 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.subInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3918) (Litex.numberInC (M := M) (1 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i8 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 h_3918) (Litex.numberInC (M := M) (1 : ℂ)) h_3813) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))

          have h_3818 : (let _equal_wd_1_0 := _object_w31;
          let _equal_wd_1_1 := _object_w34;
          Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) = (M.divValue (M.addValue (Litex.denote _value_i8) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i8) (M.number (1 : ℂ)))) from by
                    have _litex_residual : (M.divValue (M.addValue (Litex.denote _value_i8) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i8) (M.number (1 : ℂ)))) = (M.divValue (M.addValue (Litex.denote _value_i8) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i8) (M.number (1 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) = (M.divValue (M.addValue (Litex.denote _value_i8) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i8) (M.number (1 : ℂ)))) from by
                    let _litex_original := _object_w31
                    let _litex_literal := (let _wd_1_0 := (_object_i2 (M := M));
                    let _wd_1_1 := _value_i8;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_3918 h_3813))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_353 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (fun (_raw_i3 : M.Value) => (M.divValue (M.addValue _raw_i3 (M.number (1 : ℂ))) (M.subValue _raw_i3 (M.number (1 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i3 : M.Value) => (M.divValue (M.addValue _raw_i3 (M.number (1 : ℂ))) (M.subValue _raw_i3 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (Litex.denote _value_i8) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i8) (M.number (1 : ℂ)))) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w35 := (let _wd_1_0 := _object_w34;
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.sub _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w34
            exact (Litex.divInC (_object_w34).val.left (_object_w34).val.right (Litex.addInC _value_i8 _wd_1_1 (M.real_subset_complex _ h_3918) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i8 _wd_1_1 (M.real_subset_complex _ h_3918) (Litex.numberInC (M := M) (1 : ℂ))) (_atomic_wd_1_0).wd.2.2)) (Litex.numberInC (M := M) (1 : ℂ))))

          have h_3819 : (by
            let _atomic_wd_1_0 := _object_w35
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w35
                    exact (fun _litex_equal => (Litex.subNonzeroOfNotSame (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.divInC (_object_w34).val.left (_object_w34).val.right (_object_w34).wd.1 (_object_w34).wd.2.1 (_object_w34).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ)) (by
                      let _atomic_wd_2_0 := _object_w34
                      exact (Litex.notSameOfSame (_object_w32).val.left _atomic_wd_2_0 (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) h_3818 (show @Eq M.Value _ _ from Eq.refl _) h_3816))) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          have h_3820 : (by
            let _chain_wd_3820_0 := (let _wd_1_0 := _object_w31;
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (_object_i2 (M := M)) _wd_1_0 (h_352 (M := M)) (by
              let _atomic_wd_1_0 := _object_w31
              exact (by
                let _litex_return_call := _object_w31
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
              let _atomic_wd_1_0 := _object_w31
              exact h_3816)))
            let _chain_wd_3820_1 := (let _wd_1_0 := (let _wd_2_0 := _object_w31;
            let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
            (Litex.add _wd_2_0 _wd_2_1 (by
              let _atomic_wd_1_0 := _object_w31
              exact (Litex.realToComplex _object_w31 (Litex.callInOutput _object_w31))) (Litex.numberInC (M := M) (1 : ℂ))));
            let _wd_1_1 := _object_w32;
            (Litex.div _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.addInC (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_w31 (Litex.callInOutput _object_w31)) (Litex.numberInC (M := M) (1 : ℂ)))) (by
              let _atomic_wd_1_0 := _object_w32
              exact (Litex.subInC (_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_w31 (Litex.callInOutput _object_w31)) (Litex.numberInC (M := M) (1 : ℂ)))) (by
              let _atomic_wd_1_0 := _object_w32
              exact h_3817)))
            let _chain_wd_3820_2 := _chain_wd_3820_1
            let _chain_wd_3820_3 := (let _wd_1_0 := (let _wd_2_0 := _object_w34;
            let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
            (Litex.add _wd_2_0 _wd_2_1 (by
              let _atomic_wd_1_0 := _object_w34
              exact (Litex.divInC (_object_w34).val.left (_object_w34).val.right (Litex.addInC _value_i8 _wd_2_1 (M.real_subset_complex _ h_3918) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i8 _wd_2_1 (M.real_subset_complex _ h_3918) (Litex.numberInC (M := M) (1 : ℂ))) (_atomic_wd_1_0).wd.2.2)) (Litex.numberInC (M := M) (1 : ℂ))));
            let _wd_1_1 := _object_w35;
            (Litex.div _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.addInC (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.divInC (_object_w34).val.left (_object_w34).val.right (Litex.addInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3918) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3918) (Litex.numberInC (M := M) (1 : ℂ))) ((_atomic_wd_1_0).val.left).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ)))) (by
              let _atomic_wd_1_0 := _object_w35
              exact (Litex.subInC (_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.divInC (_object_w34).val.left (_object_w34).val.right (Litex.addInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3918) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3918) (Litex.numberInC (M := M) (1 : ℂ))) ((_wd_1_0).val.left).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ)))) (by
              let _atomic_wd_1_0 := _object_w35
              exact h_3819)))
            let _chain_wd_3820_4 := _chain_wd_3820_3
            exact ((let _equal_wd_1_0 := _chain_wd_3820_0;
            let _equal_wd_1_1 := _chain_wd_3820_1;
            Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ (((let _equal_wd_1_0 := _chain_wd_3820_2;
            let _equal_wd_1_1 := _chain_wd_3820_3;
            Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((let _equal_wd_1_0 := _chain_wd_3820_4;
            Litex.Same _equal_wd_1_0 _value_i8)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _chain_wd_3820_0 := (let _wd_1_0 := _object_w31;
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (_object_i2 (M := M)) _wd_1_0 (h_352 (M := M)) (by
                      let _atomic_wd_1_0 := _object_w31
                      exact (by
                        let _litex_return_call := _object_w31
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
                      let _atomic_wd_1_0 := _object_w31
                      exact h_3816)))
                    let _chain_wd_3820_1 := (let _wd_1_0 := (let _wd_2_0 := _object_w31;
                    let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.add _wd_2_0 _wd_2_1 (by
                      let _atomic_wd_1_0 := _object_w31
                      exact (Litex.realToComplex _object_w31 (Litex.callInOutput _object_w31))) (Litex.numberInC (M := M) (1 : ℂ))));
                    let _wd_1_1 := _object_w32;
                    (Litex.div _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.addInC (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_w31 (Litex.callInOutput _object_w31)) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                      let _atomic_wd_1_0 := _object_w32
                      exact (Litex.subInC (_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _object_w31 (Litex.callInOutput _object_w31)) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                      let _atomic_wd_1_0 := _object_w32
                      exact h_3817)))
                    let _chain_wd_3820_2 := _chain_wd_3820_1
                    let _chain_wd_3820_3 := (let _wd_1_0 := (let _wd_2_0 := _object_w34;
                    let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
                    (Litex.add _wd_2_0 _wd_2_1 (by
                      let _atomic_wd_1_0 := _object_w34
                      exact (Litex.divInC (_object_w34).val.left (_object_w34).val.right (Litex.addInC _value_i8 _wd_2_1 (M.real_subset_complex _ h_3918) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i8 _wd_2_1 (M.real_subset_complex _ h_3918) (Litex.numberInC (M := M) (1 : ℂ))) (_atomic_wd_1_0).wd.2.2)) (Litex.numberInC (M := M) (1 : ℂ))));
                    let _wd_1_1 := _object_w35;
                    (Litex.div _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.addInC (_atomic_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.divInC (_object_w34).val.left (_object_w34).val.right (Litex.addInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3918) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3918) (Litex.numberInC (M := M) (1 : ℂ))) ((_atomic_wd_1_0).val.left).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                      let _atomic_wd_1_0 := _object_w35
                      exact (Litex.subInC (_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.divInC (_object_w34).val.left (_object_w34).val.right (Litex.addInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3918) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.subInC _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3918) (Litex.numberInC (M := M) (1 : ℂ))) ((_wd_1_0).val.left).wd.2.2) (Litex.numberInC (M := M) (1 : ℂ)))) (by
                      let _atomic_wd_1_0 := _object_w35
                      exact h_3819)))
                    let _chain_wd_3820_4 := _chain_wd_3820_3
                    exact (And.intro (let _equal_wd_1_0 := _chain_wd_3820_0;
                    let _equal_wd_1_1 := _chain_wd_3820_1;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8))) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) (M.number (1 : ℂ)))) from by
                      have _litex_residual : (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) (M.number (1 : ℂ)))) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) (M.number (1 : ℂ)))) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8))) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) (M.number (1 : ℂ)))) from by
                      let _litex_original := _equal_wd_1_0
                      let _litex_literal := (let _wd_1_0 := (_object_i2 (M := M));
                      let _wd_1_1 := _object_w31;
                      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (by
                        let _atomic_wd_1_0 := _object_w31
                        exact (by
                          let _litex_return_call := _object_w31
                          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))) (by
                        let _atomic_wd_1_0 := _object_w31
                        exact h_3816)))
                      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_353 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) (fun (_raw_i3 : M.Value) => (M.divValue (M.addValue _raw_i3 (M.number (1 : ℂ))) (M.subValue _raw_i3 (M.number (1 : ℂ))))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (¬ (_raw_i3 = (M.number (1 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i3 : M.Value) => (M.divValue (M.addValue _raw_i3 (M.number (1 : ℂ))) (M.subValue _raw_i3 (M.number (1 : ℂ))))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) (M.number (1 : ℂ))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) (M.number (1 : ℂ)))) from rfl))
                    ))).trans _litex_residual))) (And.intro (congrArg₂ M.divValue (show (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) (M.number (1 : ℂ))) = (M.addValue (M.divValue (M.addValue (Litex.denote _value_i8) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i8) (M.number (1 : ℂ)))) (M.number (1 : ℂ))) from (congrArg₂ M.addValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) = (M.divValue (M.addValue (Litex.denote _value_i8) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i8) (M.number (1 : ℂ)))) from h_3818) (show (M.number (1 : ℂ)) = (M.number (1 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))) (show (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) (M.number (1 : ℂ))) = (M.subValue (M.divValue (M.addValue (Litex.denote _value_i8) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i8) (M.number (1 : ℂ)))) (M.number (1 : ℂ))) from (congrArg₂ M.subValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i8)) = (M.divValue (M.addValue (Litex.denote _value_i8) (M.number (1 : ℂ))) (M.subValue (Litex.denote _value_i8) (M.number (1 : ℂ)))) from h_3818) (show (M.number (1 : ℂ)) = (M.number (1 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _))))) (let _equal_wd_1_0 := _chain_wd_3820_4;
                    (show Litex.Same _equal_wd_1_0 _value_i8 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3918)) + (1 : ℂ)) / ((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3918)) - (1 : ℂ))) + (1 : ℂ)) / ((((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3918)) + (1 : ℂ)) / ((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3918)) - (1 : ℂ))) - (1 : ℂ))) (Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3918)) (Litex.NativeBridge.denoteDiv (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd ((_equal_wd_1_0).val.left).val.left (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteDiv (_object_w34).val.left (_object_w34).val.right (_object_w34).wd.1 (_object_w34).wd.2.1 (_object_w34).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd _value_i8 (Litex.number (M := M) (1 : ℂ)) ((_object_w34).val.left).wd.1 ((_object_w34).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_3918)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteSub _value_i8 (Litex.number (M := M) (1 : ℂ)) ((_object_w34).val.right).wd.1 ((_object_w34).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_3918)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteSub (_object_w35).val.left (Litex.number (M := M) (1 : ℂ)) (_object_w35).wd.1 (_object_w35).wd.2 _ _ (Litex.NativeBridge.denoteDiv (_object_w34).val.left (_object_w34).val.right (_object_w34).wd.1 (_object_w34).wd.2.1 (_object_w34).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd _value_i8 (Litex.number (M := M) (1 : ℂ)) ((_object_w34).val.left).wd.1 ((_object_w34).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_3918)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteSub _value_i8 (Litex.number (M := M) (1 : ℂ)) ((_object_w34).val.right).wd.1 ((_object_w34).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_3918)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_3918)) (by
                      have _litex_nz_0 : (((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3918)) - (1 : ℂ)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (_object_w34).val.right ((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3918)) - (1 : ℂ)) (Litex.NativeBridge.denoteSub _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_3918) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_3918)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by
                      let _atomic_wd_1_0 := (_object_w34).val.right
                      exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i8 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i8 h_3918) (Litex.numberInC (M := M) (1 : ℂ)) h_3813) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                      have _litex_nz_1 : (((((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3918)) + (1 : ℂ)) / ((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3918)) - (1 : ℂ))) - (1 : ℂ)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (_equal_wd_1_0).val.right ((((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3918)) + (1 : ℂ)) / ((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_3918)) - (1 : ℂ))) - (1 : ℂ)) (Litex.NativeBridge.denoteSub (_object_w35).val.left (Litex.number (M := M) (1 : ℂ)) (_object_w35).wd.1 (_object_w35).wd.2 _ _ (Litex.NativeBridge.denoteDiv (_object_w34).val.left (_object_w34).val.right (_object_w34).wd.1 (_object_w34).wd.2.1 (_object_w34).wd.2.2 _ _ (Litex.NativeBridge.denoteAdd _value_i8 (Litex.number (M := M) (1 : ℂ)) ((_object_w34).val.left).wd.1 ((_object_w34).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_3918)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteSub _value_i8 (Litex.number (M := M) (1 : ℂ)) ((_object_w34).val.right).wd.1 ((_object_w34).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_3918)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by
                      let _atomic_wd_1_0 := _object_w35
                      exact h_3819)
                      litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | exact _litex_nz_1 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                    )))))))
                )
            )

          have h_12637 :=
            (And.left h_3820)

          have h_12638 :=
            (And.left (And.right h_3820))

          have h_12639 :=
            (And.right (And.right h_3820))

          have h_12640 :=
            h_12637

          have h_12641 :=
            h_12638

          have h_12642 :=
            h_12639

          have h_12643 :=
            (Eq.trans h_12637 h_12638)

          have h_12644 :=
            (Eq.trans (Eq.trans h_12637 h_12638) h_12639)

          have h_12645 :=
            (Eq.trans h_12638 h_12639)
          exact h_12644
        )
      )
  )
end LitexCompiled.file_showcases_x2f_litex_x5f_to_x5f_lean_x5f_adapter_x2f_mobius_x2e_lit
