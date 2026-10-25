import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_equal_x5f_shift_x5f_functions_x2f_statement_x2e_lit

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
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_54 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_i3 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.addValue (M.number (1 : ℂ)) _raw_i4)) (by
  intro _raw_i4 h_68 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_68)
  have h_68 : Litex.In _value_i4 (Litex.R (M := M)) := h_68
  change (by
    let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_68))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_68))
    exact (Litex.addInR (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) h_68))))
theorem h_122 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i3 (M := M)))
      )
  )
theorem h_123 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i3 (M := M)))
      )
  )

theorem h_125 : Litex.Same (_object_i1 (M := M)) (_object_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          have _pointwise : ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_140 : Litex.In _value_i5 (Litex.R (M := M))), (by
            let _object_w10 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i5 (h_53 (M := M)) h_140 True.intro)
            let _object_w11 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i5 (h_122 (M := M)) h_140 True.intro)
            exact (by
              let _equal_wd_1_0 := _object_w10
              let _equal_wd_1_1 := _object_w11
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
          ) := (by
            intro _Host_i5 _rep_i5 _value_i5 h_140
            let _object_w10 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i5 (h_53 (M := M)) h_140 True.intro)
            let _object_w11 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (_object_i3 (M := M)) _value_i5 (h_122 (M := M)) h_140 True.intro)
            have h_127 : (by
              let _equal_wd_1_0 := _object_w10
              let _equal_wd_1_1 := _object_w11
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (let _equal_wd_1_0 := _object_w10;
                    let _equal_wd_1_1 := _object_w11;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote _value_i5)) from by
                      have _litex_residual : (M.addValue (Litex.denote _value_i5) (M.number (1 : ℂ))) = (M.addValue (M.number (1 : ℂ)) (Litex.denote _value_i5)) := (let _equal_wd_2_0 := (Litex.add _value_i5 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_140) (Litex.numberInC (M := M) (1 : ℂ)));
                      let _equal_wd_2_1 := (Litex.add (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_140));
                      (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i5 (Litex.realToComplex _value_i5 h_140)) + (1 : ℂ)) ((1 : ℂ) + (Litex.NativeBridge.asComplex _value_i5 (Litex.realToComplex _value_i5 h_140))) (Litex.NativeBridge.denoteAdd _value_i5 (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.realToComplex _value_i5 h_140)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) _value_i5 (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.realToComplex _value_i5 h_140))) (by ring!))))
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)) = (M.addValue (Litex.denote _value_i5) (M.number (1 : ℂ))) from by
                      let _litex_original := _equal_wd_1_0
                      let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                      let _wd_1_1 := _value_i5;
                      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_140 True.intro))
                      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_54 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.addValue _raw_i2 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (Litex.denote _value_i5) (M.number (1 : ℂ))) from rfl))
                    ))).trans (_litex_residual.trans ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote _value_i5)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote _value_i5)) = (M.addValue (M.number (1 : ℂ)) (Litex.denote _value_i5)) from by
                      let _litex_original := _equal_wd_1_1
                      let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
                      let _wd_1_1 := _value_i5;
                      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_140 True.intro))
                      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_123 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.addValue (M.number (1 : ℂ)) _raw_i4)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.addValue (M.number (1 : ℂ)) _raw_i4)) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.number (1 : ℂ)) (Litex.denote _value_i5)) from rfl))
                    ))).symm))))
                  )
              )
            exact h_127
          )
          apply Litex.functionExtOnDomain (_object_i1 (M := M)) (_object_i3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_54 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.inOfSame (_object_i3 (M := M)) (_object_i3 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) ((h_123 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i3 (M := M)))) (by rfl)
          intro _preimage_input _preimage_domain
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _).mp _preimage_domain
          have _preimage_base : M.mem _preimage_input (Litex.denote (Litex.R (M := M))) := _preimage_members
          have _repack : _preimage_input = _preimage_input := rfl
          exact Eq.mpr (congrArg (fun x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) x = Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) x) _repack) (_pointwise (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)) _preimage_base)
        )
      )
  )

noncomputable def _object_i6 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) (fun (_raw_i7 : M.Value) => _raw_i7) (by
  intro _raw_i7 h_290 h_248
  let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_290)
  have h_290 : Litex.In _value_i7 (Litex.R (M := M)) := h_290
  have h_248 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i7 = (M.number (0 : ℂ))))
            exact h_248)
        )
    )
  change Litex.In _value_i7 (Litex.R (M := M))
  exact h_290))
theorem h_297 : Litex.In (_object_i6 (M := M)) (Litex.fnSet ((_object_i6 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i6 (M := M)))
      )
  )
theorem h_298 : Litex.Same (_object_i6 (M := M)) (_object_i6 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i6 (M := M)))
      )
  )

noncomputable def _object_i9 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))) (fun (_raw_i10 : M.Value) => (M.addValue _raw_i10 (M.number (0 : ℂ)))) (by
  intro _raw_i10 h_341 h_299
  let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_341)
  have h_341 : Litex.In _value_i10 (Litex.R (M := M)) := h_341
  have h_299 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i10 = (M.number (0 : ℂ))))
            exact h_299)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i10 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_341) (Litex.numberInC (M := M) (0 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i10 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_341) (Litex.numberInC (M := M) (0 : ℂ)))
    exact (Litex.addInC _value_i10 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_341) (Litex.numberInC (M := M) (0 : ℂ))))))
theorem h_430 : Litex.In (_object_i9 (M := M)) (Litex.fnSet ((_object_i9 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i9 (M := M)))
      )
  )
theorem h_431 : Litex.Same (_object_i9 (M := M)) (_object_i9 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i9 (M := M)))
      )
  )

theorem h_433 : Litex.Same (_object_i6 (M := M)) (_object_i9 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          have _pointwise : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_449 : Litex.In _value_i12 (Litex.R (M := M))) (h_434 : ¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ))), (by
            let _object_w28 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) (_object_i6 (M := M)) _value_i12 (h_297 (M := M)) h_449 h_434)
            let _object_w29 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))) (_object_i9 (M := M)) _value_i12 (h_430 (M := M)) h_449 h_434)
            exact (by
              let _equal_wd_1_0 := _object_w28
              let _equal_wd_1_1 := _object_w29
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
          ) := (by
            intro _Host_i12 _rep_i12 _value_i12 h_449 h_434
            let _object_w28 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) (_object_i6 (M := M)) _value_i12 (h_297 (M := M)) h_449 h_434)
            let _object_w29 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))) (_object_i9 (M := M)) _value_i12 (h_430 (M := M)) h_449 h_434)
            have h_436 : (by
              let _equal_wd_1_0 := _object_w28
              let _equal_wd_1_1 := _object_w29
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (let _equal_wd_1_0 := _object_w28;
                    let _equal_wd_1_1 := _object_w29;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i6 (M := M))) (Litex.denote _value_i12)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (Litex.denote _value_i12)) from by
                      have _litex_residual : (Litex.denote _value_i12) = (M.addValue (Litex.denote _value_i12) (M.number (0 : ℂ))) := (let _equal_wd_2_1 := (Litex.add _value_i12 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_449) (Litex.numberInC (M := M) (0 : ℂ)));
                      (show Litex.Same _value_i12 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (Litex.NativeBridge.asComplex _value_i12 (Litex.realToComplex _value_i12 h_449)) ((Litex.NativeBridge.asComplex _value_i12 (Litex.realToComplex _value_i12 h_449)) + (0 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.realToComplex _value_i12 h_449)) (Litex.NativeBridge.denoteAdd _value_i12 (Litex.number (M := M) (0 : ℂ)) (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.realToComplex _value_i12 h_449)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (by ring!))))
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i6 (M := M))) (Litex.denote _value_i12)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i6 (M := M))) (Litex.denote _value_i12)) = (Litex.denote _value_i12) from by
                      let _litex_original := _equal_wd_1_0
                      let _litex_literal := (let _wd_1_0 := (_object_i6 (M := M));
                      let _wd_1_1 := _value_i12;
                      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_449 h_434))
                      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_298 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) (fun (_raw_i7 : M.Value) => _raw_i7) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i7 : M.Value) => _raw_i7) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i12) from rfl))
                    ))).trans (_litex_residual.trans ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (Litex.denote _value_i12)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (Litex.denote _value_i12)) = (M.addValue (Litex.denote _value_i12) (M.number (0 : ℂ))) from by
                      let _litex_original := _equal_wd_1_1
                      let _litex_literal := (let _wd_1_0 := (_object_i9 (M := M));
                      let _wd_1_1 := _value_i12;
                      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_449 h_434))
                      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_431 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))) (fun (_raw_i10 : M.Value) => (M.addValue _raw_i10 (M.number (0 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i10 : M.Value) => (M.addValue _raw_i10 (M.number (0 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (Litex.denote _value_i12) (M.number (0 : ℂ))) from rfl))
                    ))).symm))))
                  )
              )
            exact h_436
          )
          apply Litex.functionExtOnDomain (_object_i6 (M := M)) (_object_i9 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ)))))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ)))))) (Litex.inOfSame (_object_i6 (M := M)) (_object_i6 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))))) ((h_298 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i6 (M := M)))) (Litex.inOfSame (_object_i9 (M := M)) (_object_i9 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.complex (fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))))) ((h_431 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i9 (M := M)))) (by rfl)
          intro _preimage_input _preimage_domain
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) _litex_input) _).mp _preimage_domain
          have _preimage_guard_0 := _preimage_guard
          have _preimage_base : M.mem _preimage_input (Litex.denote (Litex.R (M := M))) := _preimage_members
          have _repack : _preimage_input = _preimage_input := rfl
          exact Eq.mpr (congrArg (fun x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i6 (M := M))) x = Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) x) _repack) (_pointwise (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)) _preimage_base _preimage_guard_0)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_equal_x5f_shift_x5f_functions_x2f_statement_x2e_lit
