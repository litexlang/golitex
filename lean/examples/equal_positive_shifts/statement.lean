import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_equal_x5f_positive_x5f_shifts_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.R (M := M))) (h_1 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1), Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_16 h_1
          have h_2 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_1
                )
            )
          exact h_2
        )
      )
  )

noncomputable def _object_i2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)) (fun (_raw_i3 : M.Value) => (M.addValue _raw_i3 (M.number (1 : ℂ)))) (by
  intro _raw_i3 h_87 h_36
  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_87)
  have h_87 : Litex.In _value_i3 (Litex.R (M := M)) := h_87
  have h_36 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)
            exact h_36)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_87) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_87) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInR _value_i3 (Litex.number (M := M) (1 : ℂ)) h_87 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))))
theorem h_142 : Litex.In (_object_i2 (M := M)) (Litex.fnSet ((_object_i2 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i2 (M := M)))
      )
  )
theorem h_143 : Litex.Same (_object_i2 (M := M)) (_object_i2 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i2 (M := M)))
      )
  )

noncomputable def _object_i5 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)) (fun (_raw_i6 : M.Value) => (M.addValue (M.number (1 : ℂ)) _raw_i6)) (by
  intro _raw_i6 h_199 h_144
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_199)
  have h_199 : Litex.In _value_i6 (Litex.R (M := M)) := h_199
  have h_144 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)
            exact h_144)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_199))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_199))
    exact (Litex.addInR (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) h_199))))
theorem h_273 : Litex.In (_object_i5 (M := M)) (Litex.fnSet ((_object_i5 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i5 (M := M)))
      )
  )
theorem h_274 : Litex.Same (_object_i5 (M := M)) (_object_i5 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i5 (M := M)))
      )
  )

theorem h_276 : Litex.Same (_object_i2 (M := M)) (_object_i5 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_280 : ∀ {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_293 : Litex.In _value_i8 (Litex.R (M := M))) (h_277 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i8), ((Litex.In _value_i8 (Litex.R (M := M))) ∧ (Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i8)) := (by
            intro _Host_i8 _rep_i8 _value_i8 h_293 h_277
            have h_278 : Litex.In _value_i8 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_293
                  )
              )
            have h_279 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i8 :=
              (by
                litex_checked_step =>
                  exact (
                    h_277
                  )
              )
            exact (And.intro h_278 h_279)
          )
          have h_330 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_343 : Litex.In _value_i9 (Litex.R (M := M))) (h_327 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9), ((Litex.In _value_i9 (Litex.R (M := M))) ∧ (Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9)) := (by
            intro _Host_i9 _rep_i9 _value_i9 h_343 h_327
            have h_328 : Litex.In _value_i9 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_343
                  )
              )
            have h_329 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
              (by
                litex_checked_step =>
                  exact (
                    h_327
                  )
              )
            exact (And.intro h_328 h_329)
          )
          have _pointwise : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_395 : Litex.In _value_i10 (Litex.R (M := M))) (h_378 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i10), (by
            let _object_w23 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i2 (M := M)) _value_i10 (h_142 (M := M)) h_395 h_378)
            let _object_w24 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i10 (h_273 (M := M)) h_395 h_378)
            exact (by
              let _equal_wd_1_0 := _object_w23
              let _equal_wd_1_1 := _object_w24
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
          ) := (by
            intro _Host_i10 _rep_i10 _value_i10 h_395 h_378
            let _object_w23 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i2 (M := M)) _value_i10 (h_142 (M := M)) h_395 h_378)
            let _object_w24 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)) (_object_i5 (M := M)) _value_i10 (h_273 (M := M)) h_395 h_378)
            have h_380 : (by
              let _equal_wd_1_0 := _object_w23
              let _equal_wd_1_1 := _object_w24
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (let _equal_wd_1_0 := _object_w23;
                    let _equal_wd_1_1 := _object_w24;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i10)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i10)) from by
                      have _litex_residual : (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ))) = (M.addValue (M.number (1 : ℂ)) (Litex.denote _value_i10)) := (let _equal_wd_2_0 := (Litex.add _value_i10 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_395) (Litex.numberInC (M := M) (1 : ℂ)));
                      let _equal_wd_2_1 := (Litex.add (Litex.number (M := M) (1 : ℂ)) _value_i10 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_395));
                      (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i10 (Litex.realToComplex _value_i10 h_395)) + (1 : ℂ)) ((1 : ℂ) + (Litex.NativeBridge.asComplex _value_i10 (Litex.realToComplex _value_i10 h_395))) (Litex.NativeBridge.denoteAdd _value_i10 (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.realToComplex _value_i10 h_395)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) _value_i10 (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.realToComplex _value_i10 h_395))) (by ring!))))
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i10)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i10)) = (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ))) from by
                      let _litex_original := _equal_wd_1_0
                      let _litex_literal := (let _wd_1_0 := (_object_i2 (M := M));
                      let _wd_1_1 := _value_i10;
                      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_395 h_378))
                      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_143 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)) (fun (_raw_i3 : M.Value) => (M.addValue _raw_i3 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i3 : M.Value) => (M.addValue _raw_i3 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (Litex.denote _value_i10) (M.number (1 : ℂ))) from rfl))
                    ))).trans (_litex_residual.trans ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i10)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote _value_i10)) = (M.addValue (M.number (1 : ℂ)) (Litex.denote _value_i10)) from by
                      let _litex_original := _equal_wd_1_1
                      let _litex_literal := (let _wd_1_0 := (_object_i5 (M := M));
                      let _wd_1_1 := _value_i10;
                      (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_395 h_378))
                      have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_274 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                      have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)) (fun (_raw_i6 : M.Value) => (M.addValue (M.number (1 : ℂ)) _raw_i6)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i6 : M.Value) => (M.addValue (M.number (1 : ℂ)) _raw_i6)) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.number (1 : ℂ)) (Litex.denote _value_i10)) from rfl))
                    ))).symm))))
                  )
              )
            exact h_380
          )
          apply Litex.functionExtOnDomain (_object_i2 (M := M)) (_object_i5 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s))) (Litex.inOfSame (_object_i2 (M := M)) (_object_i2 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_143 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i2 (M := M)))) (Litex.inOfSame (_object_i5 (M := M)) (_object_i5 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)))) ((h_274 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i5 (M := M)))) (Litex.SetSemantics.ext ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)))).domain ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)))).domain_isSet ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)))).domain_isSet (fun x => ⟨fun hx => (show ∀ x : M.Value, M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)))).domain → M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)))).domain from by
            intro _preimage_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)) _litex_input) _).mp _preimage_domain
            have _preimage_guard_0 := _preimage_guard
            have _preimage_base : M.mem _preimage_input (Litex.denote (Litex.R (M := M))) := _preimage_members
            have _domain_target := h_280 (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)) _preimage_base _preimage_guard_0
            have _repack : _preimage_input = (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base))) := (show _preimage_input = _preimage_input from rfl)
            exact Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)))).domain) _repack) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)))).mpr ⟨(And.left _domain_target), (And.right _domain_target)⟩)
          ) x hx, fun hx => (show ∀ x : M.Value, M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)))).domain → M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)))).domain from by
            intro _preimage_input _preimage_domain
            obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)) _litex_input) _).mp _preimage_domain
            have _preimage_guard_0 := _preimage_guard
            have _preimage_base : M.mem _preimage_input (Litex.denote (Litex.R (M := M))) := _preimage_members
            have _domain_target := h_330 (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)) _preimage_base _preimage_guard_0
            have _repack : _preimage_input = (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base))) := (show _preimage_input = _preimage_input from rfl)
            exact Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)))).domain) _repack) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.denote (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)))).mpr ⟨(And.left _domain_target), (And.right _domain_target)⟩)
          ) x hx⟩))
          intro _preimage_input _preimage_domain
          obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i3 = M.number (_s : ℂ) ∧ _r < _s)) _litex_input) _).mp _preimage_domain
          have _preimage_guard_0 := _preimage_guard
          have _preimage_base : M.mem _preimage_input (Litex.denote (Litex.R (M := M))) := _preimage_members
          have _repack : _preimage_input = _preimage_input := rfl
          exact Eq.mpr (congrArg (fun x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) x = Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) x) _repack) (_pointwise (Litex.semanticObject _preimage_input (M.member_isSet _preimage_base)) _preimage_base _preimage_guard_0)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_equal_x5f_positive_x5f_shifts_x2f_statement_x2e_lit
