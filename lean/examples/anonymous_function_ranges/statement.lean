import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_anonymous_x5f_function_x5f_ranges_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_w3 := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
  intro _raw_i1 h_15 _
  let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_15)
  have h_15 : Litex.In _value_i1 (Litex.R (M := M)) := h_15
  change Litex.In _value_i1 (Litex.R (M := M))
  exact h_15));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro))

noncomputable def _object_w4 := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
  intro _raw_i2 h_35 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_35)
  have h_35 : Litex.In _value_i2 (Litex.R (M := M)) := h_35
  change Litex.In _value_i2 (Litex.R (M := M))
  exact h_35));
(by
  have _range_signature_0 : Litex.In _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) := (Litex.inOfSame _wd_1_0 _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet _wd_1_0))
  exact Litex.fnRange _wd_1_0 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) _range_signature_0))

theorem h_1 : (by
  let _atomic_wd_1_0 := (_object_w3 (M := M))
  let _atomic_wd_1_1 := (_object_w4 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w3 (M := M))
          let _atomic_wd_1_1 := (_object_w4 (M := M))
          exact (Litex.callInFnRange _atomic_wd_1_0 _atomic_wd_1_1 (by
            let _left : Litex.Obj (M := M) (Litex.FormulaFn M) := (_atomic_wd_1_0).val.function
            let _right : Litex.Obj (M := M) (Litex.FormulaFn M) := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
            intro _raw_i2 h_35 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_35)
            have h_35 : Litex.In _value_i2 (Litex.R (M := M)) := h_35
            change Litex.In _value_i2 (Litex.R (M := M))
            exact h_35))
            exact (show Litex.Same _left _right from rfl))))
      )
  )

theorem h_43 : Litex.In (_object_w3 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.fnRangeInOutput (_object_w4 (M := M)) (_object_w3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.formulaFnInFnSet (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
          intro _raw_i2 h_35 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_35)
          have h_35 : Litex.In _value_i2 (Litex.R (M := M)) := h_35
          change Litex.In _value_i2 (Litex.R (M := M))
          exact h_35))) (h_1 (M := M)))
      )
  )

theorem h_45 : ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (_member_i3 : M.mem (Litex.denote _value_i3) (M.standard Litex.StandardSetValue.real)), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote ((_object_w3 (M := M))).val.function) (M.number (2 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
  intro _raw_i2 h_35 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_35)
  have h_35 : Litex.In _value_i2 (Litex.R (M := M)) := h_35
  change Litex.In _value_i2 (Litex.R (M := M))
  exact h_35))) (Litex.denote _value_i3))) :=
  (by
    litex_complete =>
      exact (
        (by
          obtain ⟨_range_input, _range_domain, _range_eq⟩ := (Litex.inFnRange_iff (_object_w4 (M := M)) (_object_w3 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.formulaFnInFnSet (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => _raw_i2) (by
          intro _raw_i2 h_35 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_35)
          have h_35 : Litex.In _value_i2 (Litex.R (M := M)) := h_35
          change Litex.In _value_i2 (Litex.R (M := M))
          exact h_35)))).mp (h_1 (M := M))
          obtain ⟨_range_members, _range_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _).mp _range_domain
          have _range_base_member_0 := _range_members
          have _range_member_0 := _range_base_member_0
          exact ⟨(Litex.semanticObject (Litex.denote _range_input) (M.member_isSet _range_member_0)), _range_member_0, _range_eq⟩)
      )
  )

noncomputable def _object_w8 := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (M.divValue _raw_i4 _raw_i5)) (by
  intro _raw_i4 _raw_i5 h_116 h_117 h_46
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_116)
  have h_116 : Litex.In _value_i4 (Litex.R (M := M)) := h_116
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_117)
  have h_117 : Litex.In _value_i5 (Litex.R (M := M)) := h_117
  have h_46 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i5 = (M.number (0 : ℂ))))
            exact h_46)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.div _value_i4 _value_i5 (M.real_subset_complex _ h_116) (M.real_subset_complex _ h_117) h_46)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.div _value_i4 _value_i5 (M.real_subset_complex _ h_116) (M.real_subset_complex _ h_117) h_46)
    exact (Litex.divInR _value_i4 _value_i5 h_116 h_117 (_atomic_wd_1_0).wd.2.2))));
let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
let _wd_1_2 := (Litex.number (M := M) (2 : ℂ));
(Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_2 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

noncomputable def _object_w9 := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (M.divValue _raw_i6 _raw_i7)) (by
  intro _raw_i6 _raw_i7 h_309 h_310 h_47
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_309)
  have h_309 : Litex.In _value_i6 (Litex.R (M := M)) := h_309
  let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_310)
  have h_310 : Litex.In _value_i7 (Litex.R (M := M)) := h_310
  have h_47 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i7 = (M.number (0 : ℂ))))
            exact h_47)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.div _value_i6 _value_i7 (M.real_subset_complex _ h_309) (M.real_subset_complex _ h_310) h_47)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.div _value_i6 _value_i7 (M.real_subset_complex _ h_309) (M.real_subset_complex _ h_310) h_47)
    exact (Litex.divInR _value_i6 _value_i7 h_309 h_310 (_atomic_wd_1_0).wd.2.2))));
(by
  have _range_signature_0 : Litex.In _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))))) := (Litex.inOfSame _wd_1_0 _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet _wd_1_0))
  exact Litex.fnRange _wd_1_0 (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ)))))) _range_signature_0))

theorem h_48 : (by
  let _atomic_wd_1_0 := (_object_w8 (M := M))
  let _atomic_wd_1_1 := (_object_w9 (M := M))
  exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w8 (M := M))
          let _atomic_wd_1_1 := (_object_w9 (M := M))
          exact (Litex.call2InFnRange _atomic_wd_1_0 _atomic_wd_1_1 (by
            let _left : Litex.Obj (M := M) (Litex.FormulaFn M) := (_atomic_wd_1_0).val.function
            let _right : Litex.Obj (M := M) (Litex.FormulaFn M) := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (M.divValue _raw_i6 _raw_i7)) (by
            intro _raw_i6 _raw_i7 h_309 h_310 h_47
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_309)
            have h_309 : Litex.In _value_i6 (Litex.R (M := M)) := h_309
            let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_310)
            have h_310 : Litex.In _value_i7 (Litex.R (M := M)) := h_310
            have h_47 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      change (¬ (_raw_i7 = (M.number (0 : ℂ))))
                      exact h_47)
                  )
              )
            change (by
              let _atomic_wd_2_0 := (Litex.div _value_i6 _value_i7 (M.real_subset_complex _ h_309) (M.real_subset_complex _ h_310) h_47)
              exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_2_0 := (Litex.div _value_i6 _value_i7 (M.real_subset_complex _ h_309) (M.real_subset_complex _ h_310) h_47)
              exact (Litex.divInR _value_i6 _value_i7 h_309 h_310 (_atomic_wd_2_0).wd.2.2))))
            exact (show Litex.Same _left _right from rfl))))
      )
  )

theorem h_434 : Litex.In (_object_w8 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.fnRangeInOutput (_object_w9 (M := M)) (_object_w8 (M := M)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ)))))) (Litex.formulaFnInFnSet (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (M.divValue _raw_i6 _raw_i7)) (by
          intro _raw_i6 _raw_i7 h_309 h_310 h_47
          let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_309)
          have h_309 : Litex.In _value_i6 (Litex.R (M := M)) := h_309
          let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_310)
          have h_310 : Litex.In _value_i7 (Litex.R (M := M)) := h_310
          have h_47 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    change (¬ (_raw_i7 = (M.number (0 : ℂ))))
                    exact h_47)
                )
            )
          change (by
            let _atomic_wd_1_0 := (Litex.div _value_i6 _value_i7 (M.real_subset_complex _ h_309) (M.real_subset_complex _ h_310) h_47)
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.div _value_i6 _value_i7 (M.real_subset_complex _ h_309) (M.real_subset_complex _ h_310) h_47)
            exact (Litex.divInR _value_i6 _value_i7 h_309 h_310 (_atomic_wd_1_0).wd.2.2))))) (h_48 (M := M)))
      )
  )

theorem h_437 : ∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (_member_i12 : M.mem (Litex.denote _value_i12) (M.standard Litex.StandardSetValue.real)), ∃ (_value_i13 : Litex.Obj (M := M) M.Value), ∃ (_member_i13 : M.mem (Litex.denote _value_i13) (M.standard Litex.StandardSetValue.real)), ∃ (h_435 : (¬ ((Litex.denote _value_i13) = (M.number (0 : ℂ))))), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote ((_object_w8 (M := M))).val.function) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (3 : ℂ)), (M.number (2 : ℂ))])) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (M.divValue _raw_i6 _raw_i7)) (by
  intro _raw_i6 _raw_i7 h_309 h_310 h_47
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_309)
  have h_309 : Litex.In _value_i6 (Litex.R (M := M)) := h_309
  let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_310)
  have h_310 : Litex.In _value_i7 (Litex.R (M := M)) := h_310
  have h_47 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i7 = (M.number (0 : ℂ))))
            exact h_47)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.div _value_i6 _value_i7 (M.real_subset_complex _ h_309) (M.real_subset_complex _ h_310) h_47)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.div _value_i6 _value_i7 (M.real_subset_complex _ h_309) (M.real_subset_complex _ h_310) h_47)
    exact (Litex.divInR _value_i6 _value_i7 h_309 h_310 (_atomic_wd_1_0).wd.2.2))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i12), (Litex.denote _value_i13)]))) :=
  (by
    litex_complete =>
      exact (
        (by
          obtain ⟨_range_input, _range_domain, _range_eq⟩ := (Litex.inFnRange_iff (_object_w9 (M := M)) (_object_w8 (M := M)) (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ)))))) (Litex.formulaFnInFnSet (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (M.divValue _raw_i6 _raw_i7)) (by
          intro _raw_i6 _raw_i7 h_309 h_310 h_47
          let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_309)
          have h_309 : Litex.In _value_i6 (Litex.R (M := M)) := h_309
          let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_310)
          have h_310 : Litex.In _value_i7 (Litex.R (M := M)) := h_310
          have h_47 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    change (¬ (_raw_i7 = (M.number (0 : ℂ))))
                    exact h_47)
                )
            )
          change (by
            let _atomic_wd_1_0 := (Litex.div _value_i6 _value_i7 (M.real_subset_complex _ h_309) (M.real_subset_complex _ h_310) h_47)
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.div _value_i6 _value_i7 (M.real_subset_complex _ h_309) (M.real_subset_complex _ h_310) h_47)
            exact (Litex.divInR _value_i6 _value_i7 h_309 h_310 (_atomic_wd_1_0).wd.2.2)))))).mp (h_48 (M := M))
          obtain ⟨_range_members, _range_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
          have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
          have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _).mp _range_domain
          have h_435 := _range_guard
          have _range_base_member_0 := (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _range_members (0 : Fin 2))
          have _range_member_0 := _range_base_member_0
          have _range_base_member_1 := (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _range_members (1 : Fin 2))
          have _range_member_1 := _range_base_member_1
          have _range_repack : Litex.denote _range_input = Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote _range_input) (M.number (1 : ℂ))), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _range_input) (M.number (2 : ℂ)))] := by
            apply (Litex.FiniteFunction.reconstruct _range_members).trans
            apply congrArg (Litex.FiniteFunction.tupleValue (M := M))
            funext i
            fin_cases i <;> norm_num [Litex.FiniteFunction.index]
          exact ⟨(Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _range_input) (M.number (1 : ℂ))) (M.member_isSet _range_member_0)), _range_member_0, (Litex.semanticObject (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _range_input) (M.number (2 : ℂ))) (M.member_isSet _range_member_1)), _range_member_1, h_435, (_range_eq.trans (congrArg (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (¬ (_raw_i7 = (M.number (0 : ℂ))))) (fun (_raw_i6 : M.Value) (_raw_i7 : M.Value) => (M.divValue _raw_i6 _raw_i7)) (by
          intro _raw_i6 _raw_i7 h_309 h_310 h_47
          let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_309)
          have h_309 : Litex.In _value_i6 (Litex.R (M := M)) := h_309
          let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_310)
          have h_310 : Litex.In _value_i7 (Litex.R (M := M)) := h_310
          have h_47 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    change (¬ (_raw_i7 = (M.number (0 : ℂ))))
                    exact h_47)
                )
            )
          change (by
            let _atomic_wd_1_0 := (Litex.div _value_i6 _value_i7 (M.real_subset_complex _ h_309) (M.real_subset_complex _ h_310) h_47)
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.div _value_i6 _value_i7 (M.real_subset_complex _ h_309) (M.real_subset_complex _ h_310) h_47)
            exact (Litex.divInR _value_i6 _value_i7 h_309 h_310 (_atomic_wd_1_0).wd.2.2)))))) _range_repack))⟩)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_anonymous_x5f_function_x5f_ranges_x2f_statement_x2e_lit
