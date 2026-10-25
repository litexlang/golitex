import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_captured_x5f_division_x5f_functions_x2f_statement_x2e_lit

universe u v6 v14
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFnOn (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_44 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_44)
    have h_44 : Litex.In _value_i3 (Litex.R (M := M)) := h_44
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.divValue _raw_i4 _raw_i2)) _captured_input))) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _raw_i2) → M.mem ((fun (_raw_i2 : M.Value) => (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.divValue _raw_i4 _raw_i2)) _captured_input))) _raw_i2) (Litex.denote (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_44 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_44)
    have h_44 : Litex.In _value_i3 (Litex.R (M := M)) := h_44
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))) := (by
    intro _raw_i2 h_43 h_1
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_43)
    have h_43 : Litex.In _value_i2 (Litex.R (M := M)) := h_43
    have h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i2 = (M.number (0 : ℂ))))
              exact h_1)
          )
      )
    change (by
      let _atomic_wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.divValue _raw_i4 (Litex.denote _value_i2))) (by
        intro _raw_i4 h_154 _
        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_154)
        have h_154 : Litex.In _value_i4 (Litex.R (M := M)) := h_154
        change (by
          let _atomic_wd_2_0 := (Litex.div _value_i4 _value_i2 (M.real_subset_complex _ h_154) (M.real_subset_complex _ h_43) h_1)
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (Litex.div _value_i4 _value_i2 (M.real_subset_complex _ h_154) (M.real_subset_complex _ h_43) h_1)
          exact (Litex.divInR _value_i4 _value_i2 h_154 h_43 (_atomic_wd_2_0).wd.2.2))))
      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
          intro _raw_i3 h_236 _
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_236)
          have h_236 : Litex.In _value_i3 (Litex.R (M := M)) := h_236
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
      exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
    exact (by
      let _atomic_wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.divValue _raw_i4 (Litex.denote _value_i2))) (by
        intro _raw_i4 h_154 _
        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_154)
        have h_154 : Litex.In _value_i4 (Litex.R (M := M)) := h_154
        change (by
          let _atomic_wd_2_0 := (Litex.div _value_i4 _value_i2 (M.real_subset_complex _ h_154) (M.real_subset_complex _ h_43) h_1)
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (Litex.div _value_i4 _value_i2 (M.real_subset_complex _ h_154) (M.real_subset_complex _ h_43) h_1)
          exact (Litex.divInR _value_i4 _value_i2 h_154 h_43 (_atomic_wd_2_0).wd.2.2))))
      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
          intro _raw_i3 h_236 _
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_236)
          have h_236 : Litex.In _value_i3 (Litex.R (M := M)) := h_236
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
      exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from by exact Litex.formulaFnInFnSet _atomic_wd_1_0)))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.R (M := M))) (Litex.denote (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_44 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_44)
    have h_44 : Litex.In _value_i3 (Litex.R (M := M)) := h_44
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))) (Litex.isSet (Litex.R (M := M))) (Litex.isSet (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_44 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_44)
    have h_44 : Litex.In _value_i3 (Litex.R (M := M)) := h_44
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_243 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_244 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_248 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_261 : Litex.In _value_i6 (Litex.R (M := M))) (h_245 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w10 := (let _litex_call_arg_0 := _value_i6;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_243 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_261, h_245⟩))
  let _object_w11 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => (M.divValue _raw_i7 (Litex.denote _value_i6))) (by
    intro _raw_i7 h_285 _
    let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_285)
    have h_285 : Litex.In _value_i7 (Litex.R (M := M)) := h_285
    change (by
      let _atomic_wd_1_0 := (Litex.div _value_i7 _value_i6 (M.real_subset_complex _ h_285) (M.real_subset_complex _ h_261) h_245)
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.div _value_i7 _value_i6 (M.real_subset_complex _ h_285) (M.real_subset_complex _ h_261) h_245)
      exact (Litex.divInR _value_i7 _value_i6 h_285 h_261 (_atomic_wd_1_0).wd.2.2))))
  let _object_w12 := (by
    let _returned_receiver := (let _litex_call_arg_0 := _value_i6;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_243 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_261, h_245⟩))
    let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))
    have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
    have _returned_domain : M.mem (Litex.denote (Litex.number (M := M) (2 : ℂ))) _returned_signature.domain := ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), True.intro⟩)
    exact Litex.callOn _returned_signature _returned_receiver (Litex.number (M := M) (2 : ℂ)) _returned_member _returned_domain)
  let _object_w13 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _value_i6 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_261) h_245)
  exact (((by
    let _equal_wd_1_0 := _object_w10
    let _equal_wd_1_1 := _object_w11
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w12
    let _equal_wd_1_1 := _object_w13
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_261 h_245
          let _object_w10 := (let _litex_call_arg_0 := _value_i6;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_243 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_261, h_245⟩))
          let _object_w11 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => (M.divValue _raw_i7 (Litex.denote _value_i6))) (by
            intro _raw_i7 h_285 _
            let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_285)
            have h_285 : Litex.In _value_i7 (Litex.R (M := M)) := h_285
            change (by
              let _atomic_wd_1_0 := (Litex.div _value_i7 _value_i6 (M.real_subset_complex _ h_285) (M.real_subset_complex _ h_261) h_245)
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.div _value_i7 _value_i6 (M.real_subset_complex _ h_285) (M.real_subset_complex _ h_261) h_245)
              exact (Litex.divInR _value_i7 _value_i6 h_285 h_261 (_atomic_wd_1_0).wd.2.2))))
          have h_246 : (by
            let _equal_wd_1_0 := _object_w10
            let _equal_wd_1_1 := _object_w11
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w10;
                  let _equal_wd_1_1 := _object_w11;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.divValue _raw_i7 (Litex.denote _value_i6))) _captured_input)) from by
                    have _litex_residual : (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.divValue _raw_i4 (Litex.denote _value_i6))) _captured_input)) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.divValue _raw_i7 (Litex.denote _value_i6))) _captured_input)) := (let _equal_wd_2_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.divValue _raw_i4 (Litex.denote _value_i6))) (by
                      intro _raw_i4 h_446 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_446)
                      have h_446 : Litex.In _value_i4 (Litex.R (M := M)) := h_446
                      change (by
                        let _atomic_wd_1_0 := (Litex.div _value_i4 _value_i6 (M.real_subset_complex _ h_446) (M.real_subset_complex _ h_261) h_245)
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.div _value_i4 _value_i6 (M.real_subset_complex _ h_446) (M.real_subset_complex _ h_261) h_245)
                        exact (Litex.divInR _value_i4 _value_i6 h_446 h_261 (_atomic_wd_1_0).wd.2.2))));
                    let _equal_wd_2_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => (M.divValue _raw_i7 (Litex.denote _value_i6))) (by
                      intro _raw_i7 h_556 _
                      let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_556)
                      have h_556 : Litex.In _value_i7 (Litex.R (M := M)) := h_556
                      change (by
                        let _atomic_wd_1_0 := (Litex.div _value_i7 _value_i6 (M.real_subset_complex _ h_556) (M.real_subset_complex _ h_261) h_245)
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.div _value_i7 _value_i6 (M.real_subset_complex _ h_556) (M.real_subset_complex _ h_261) h_245)
                        exact (Litex.divInR _value_i7 _value_i6 h_556 h_261 (_atomic_wd_1_0).wd.2.2))));
                    (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (by
                      let _left : Litex.Obj (M := M) (Litex.FormulaFn M) := _equal_wd_2_0
                      let _right : Litex.Obj (M := M) (Litex.FormulaFn M) := _equal_wd_2_1
                      exact (show Litex.Same _left _right from rfl))))
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.divValue _raw_i4 (Litex.denote _value_i6))) _captured_input)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                  let _wd_1_1 := _value_i6;
                  (let _litex_call_arg_0 := _wd_1_1;
                  Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                      intro _raw_i3 h_242 _
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_242)
                      have h_242 : Litex.In _value_i3 (Litex.R (M := M)) := h_242
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) h_261 h_245))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_244 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.divValue _raw_i4 _raw_i2)) _captured_input))) _litex_input) (Litex.denote _litex_literal.val.argument) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.divValue _raw_i4 (Litex.denote _value_i6))) _captured_input)); exact rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w12 := (by
            let _returned_receiver := (let _litex_call_arg_0 := _value_i6;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_243 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_261, h_245⟩))
            let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))
            have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
            have _returned_domain : M.mem (Litex.denote (Litex.number (M := M) (2 : ℂ))) _returned_signature.domain := ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), True.intro⟩)
            exact Litex.callOn _returned_signature _returned_receiver (Litex.number (M := M) (2 : ℂ)) _returned_member _returned_domain)
          let _object_w13 := (Litex.div (Litex.number (M := M) (2 : ℂ)) _value_i6 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_261) h_245)
          have h_247 : (by
            let _equal_wd_1_0 := _object_w12
            let _equal_wd_1_1 := _object_w13
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)) (M.number (2 : ℂ))) = (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i6)) from by
                    have _litex_residual : (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i6)) = (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)) (M.number (2 : ℂ))))).trans (congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (M.number (2 : ℂ))) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i6)) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.divValue _raw_i4 (Litex.denote _value_i6))) _captured_input)) from by
                    let _litex_original := _object_w10
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                  let _wd_1_1 := _value_i6;
                  (let _litex_call_arg_0 := _wd_1_1;
                  Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                      intro _raw_i3 h_242 _
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_242)
                      have h_242 : Litex.In _value_i3 (Litex.R (M := M)) := h_242
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (¬ (_raw_i2 = (M.number (0 : ℂ))))) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) h_261 h_245))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_244 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.divValue _raw_i4 _raw_i2)) _captured_input))) _litex_input) (Litex.denote _litex_literal.val.argument) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.divValue _raw_i4 (Litex.denote _value_i6))) _captured_input)); exact rfl))
                  )))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.divValue _raw_i4 (Litex.denote _value_i6))) _captured_input)) (M.number (2 : ℂ))) = (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i6)) from by
                    let _litex_original := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.divValue _raw_i4 (Litex.denote _value_i6))) (by
                      intro _raw_i4 h_957 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_957)
                      have h_957 : Litex.In _value_i4 (Litex.R (M := M)) := h_957
                      change (by
                        let _atomic_wd_1_0 := (Litex.div _value_i4 _value_i6 (M.real_subset_complex _ h_957) (M.real_subset_complex _ h_261) h_245)
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.div _value_i4 _value_i6 (M.real_subset_complex _ h_957) (M.real_subset_complex _ h_261) h_245)
                        exact (Litex.divInR _value_i4 _value_i6 h_957 h_261 (_atomic_wd_1_0).wd.2.2))));
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro))
                    let _litex_literal := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.divValue _raw_i4 (Litex.denote _value_i6))) (by
                      intro _raw_i4 h_1072 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1072)
                      have h_1072 : Litex.In _value_i4 (Litex.R (M := M)) := h_1072
                      change (by
                        let _atomic_wd_1_0 := (Litex.div _value_i4 _value_i6 (M.real_subset_complex _ h_1072) (M.real_subset_complex _ h_261) h_245)
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.div _value_i4 _value_i6 (M.real_subset_complex _ h_1072) (M.real_subset_complex _ h_261) h_245)
                        exact (Litex.divInR _value_i4 _value_i6 h_1072 h_261 (_atomic_wd_1_0).wd.2.2))));
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.divValue _raw_i4 (Litex.denote _value_i6))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.divValue _raw_i4 (Litex.denote _value_i6))) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (2 : ℂ)) (Litex.denote _value_i6)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          exact (And.intro h_246 h_247)
        )
      )
  )

noncomputable def _object_i8 := (Litex.formulaFnOn (let _litex_output := (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))) _raw_i10) → True := (by
    intro _raw_i10 h_1239 h_1223
    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_1239)
    have h_1239 : Litex.In _value_i10 (Litex.R (M := M)) := h_1239
    have h_1223 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i10 = (M.number (0 : ℂ))))
              exact h_1223)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.divValue _raw_i9 _raw_i11)) _captured_input))) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → M.mem ((fun (_raw_i9 : M.Value) => (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.divValue _raw_i9 _raw_i11)) _captured_input))) _raw_i9) (Litex.denote (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))) _raw_i10) → True := (by
    intro _raw_i10 h_1239 h_1223
    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_1239)
    have h_1239 : Litex.In _value_i10 (Litex.R (M := M)) := h_1239
    have h_1223 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i10 = (M.number (0 : ℂ))))
              exact h_1223)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ)))))))) := (by
    intro _raw_i9 h_1238 _
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_1238)
    have h_1238 : Litex.In _value_i9 (Litex.R (M := M)) := h_1238
    change (by
      let _atomic_wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) (fun (_raw_i11 : M.Value) => (M.divValue (Litex.denote _value_i9) _raw_i11)) (by
        intro _raw_i11 h_1421 h_1224
        let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1421)
        have h_1421 : Litex.In _value_i11 (Litex.R (M := M)) := h_1421
        have h_1224 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)) :=
          (by
            litex_checked_step =>
              exact (
                (by
                  change (¬ (_raw_i11 = (M.number (0 : ℂ))))
                  exact h_1224)
              )
          )
        change (by
          let _atomic_wd_2_0 := (Litex.div _value_i9 _value_i11 (M.real_subset_complex _ h_1238) (M.real_subset_complex _ h_1421) h_1224)
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (Litex.div _value_i9 _value_i11 (M.real_subset_complex _ h_1238) (M.real_subset_complex _ h_1421) h_1224)
          exact (Litex.divInR _value_i9 _value_i11 h_1238 h_1421 (_atomic_wd_2_0).wd.2.2))))
      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))) _raw_i10) → True := (by
          intro _raw_i10 h_1519 h_1223
          let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_1519)
          have h_1519 : Litex.In _value_i10 (Litex.R (M := M)) := h_1519
          have h_1223 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    change (¬ (_raw_i10 = (M.number (0 : ℂ))))
                    exact h_1223)
                )
            )
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ)))))))
      exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
    exact (by
      let _atomic_wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) (fun (_raw_i11 : M.Value) => (M.divValue (Litex.denote _value_i9) _raw_i11)) (by
        intro _raw_i11 h_1421 h_1224
        let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1421)
        have h_1421 : Litex.In _value_i11 (Litex.R (M := M)) := h_1421
        have h_1224 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)) :=
          (by
            litex_checked_step =>
              exact (
                (by
                  change (¬ (_raw_i11 = (M.number (0 : ℂ))))
                  exact h_1224)
              )
          )
        change (by
          let _atomic_wd_2_0 := (Litex.div _value_i9 _value_i11 (M.real_subset_complex _ h_1238) (M.real_subset_complex _ h_1421) h_1224)
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (Litex.div _value_i9 _value_i11 (M.real_subset_complex _ h_1238) (M.real_subset_complex _ h_1421) h_1224)
          exact (Litex.divInR _value_i9 _value_i11 h_1238 h_1421 (_atomic_wd_2_0).wd.2.2))))
      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))) _raw_i10) → True := (by
          intro _raw_i10 h_1519 h_1223
          let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_1519)
          have h_1519 : Litex.In _value_i10 (Litex.R (M := M)) := h_1519
          have h_1223 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    change (¬ (_raw_i10 = (M.number (0 : ℂ))))
                    exact h_1223)
                )
            )
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ)))))))
      exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from by exact Litex.formulaFnInFnSet _atomic_wd_1_0)))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.R (M := M))) (Litex.denote (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))) _raw_i10) → True := (by
    intro _raw_i10 h_1239 h_1223
    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_1239)
    have h_1239 : Litex.In _value_i10 (Litex.R (M := M)) := h_1239
    have h_1223 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i10 = (M.number (0 : ℂ))))
              exact h_1223)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ)))))))) (Litex.isSet (Litex.R (M := M))) (Litex.isSet (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))) _raw_i10) → True := (by
    intro _raw_i10 h_1239 h_1223
    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_1239)
    have h_1239 : Litex.In _value_i10 (Litex.R (M := M)) := h_1239
    have h_1223 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i10 = (M.number (0 : ℂ))))
              exact h_1223)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ)))))))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_1530 : Litex.In (_object_i8 (M := M)) (Litex.fnSet ((_object_i8 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i8 (M := M)))
      )
  )
theorem h_1531 : Litex.Same (_object_i8 (M := M)) (_object_i8 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i8 (M := M)))
      )
  )

theorem h_1535 : ∀ {_Host_i14 : Type v14} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_1548 : Litex.In _value_i14 (Litex.R (M := M))), (by
  let _object_w27 := (let _litex_call_arg_0 := _value_i14;
  Litex.callOn ((_object_i8 (M := M))).val.signature (_object_i8 (M := M)) _litex_call_arg_0 (h_1530 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_1548, True.intro⟩))
  let _object_w28 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i15 : M.Value) => (¬ (_raw_i15 = (M.number (0 : ℂ))))) (fun (_raw_i15 : M.Value) => (M.divValue (Litex.denote _value_i14) _raw_i15)) (by
    intro _raw_i15 h_1595 h_1532
    let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_1595)
    have h_1595 : Litex.In _value_i15 (Litex.R (M := M)) := h_1595
    have h_1532 : ¬ Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i15 = (M.number (0 : ℂ))))
              exact h_1532)
          )
      )
    change (by
      let _atomic_wd_1_0 := (Litex.div _value_i14 _value_i15 (M.real_subset_complex _ h_1548) (M.real_subset_complex _ h_1595) h_1532)
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.div _value_i14 _value_i15 (M.real_subset_complex _ h_1548) (M.real_subset_complex _ h_1595) h_1532)
      exact (Litex.divInR _value_i14 _value_i15 h_1548 h_1595 (_atomic_wd_1_0).wd.2.2))))
  let _object_w31 := (by
    let _returned_receiver := (let _litex_call_arg_0 := _value_i14;
  Litex.callOn ((_object_i8 (M := M))).val.signature (_object_i8 (M := M)) _litex_call_arg_0 (h_1530 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_1548, True.intro⟩))
    let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))))
    have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
    have _returned_domain : M.mem (Litex.denote (Litex.number (M := M) (2 : ℂ))) _returned_signature.domain := ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))⟩)
    exact Litex.callOn _returned_signature _returned_receiver (Litex.number (M := M) (2 : ℂ)) _returned_member _returned_domain)
  let _object_w32 := (Litex.div _value_i14 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_1548) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  exact (((by
    let _equal_wd_1_0 := _object_w27
    let _equal_wd_1_1 := _object_w28
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w31
    let _equal_wd_1_1 := _object_w32
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i14 _rep_i14 _value_i14 h_1548
          let _object_w27 := (let _litex_call_arg_0 := _value_i14;
          Litex.callOn ((_object_i8 (M := M))).val.signature (_object_i8 (M := M)) _litex_call_arg_0 (h_1530 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_1548, True.intro⟩))
          let _object_w28 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i15 : M.Value) => (¬ (_raw_i15 = (M.number (0 : ℂ))))) (fun (_raw_i15 : M.Value) => (M.divValue (Litex.denote _value_i14) _raw_i15)) (by
            intro _raw_i15 h_1595 h_1532
            let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_1595)
            have h_1595 : Litex.In _value_i15 (Litex.R (M := M)) := h_1595
            have h_1532 : ¬ Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      change (¬ (_raw_i15 = (M.number (0 : ℂ))))
                      exact h_1532)
                  )
              )
            change (by
              let _atomic_wd_1_0 := (Litex.div _value_i14 _value_i15 (M.real_subset_complex _ h_1548) (M.real_subset_complex _ h_1595) h_1532)
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.div _value_i14 _value_i15 (M.real_subset_complex _ h_1548) (M.real_subset_complex _ h_1595) h_1532)
              exact (Litex.divInR _value_i14 _value_i15 h_1548 h_1595 (_atomic_wd_1_0).wd.2.2))))
          have h_1533 : (by
            let _equal_wd_1_0 := _object_w27
            let _equal_wd_1_1 := _object_w28
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w27;
                  let _equal_wd_1_1 := _object_w28;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i14)) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i15 : M.Value) => (¬ (_raw_i15 = (M.number (0 : ℂ))))) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i15 : M.Value) => (M.divValue (Litex.denote _value_i14) _raw_i15)) _captured_input)) from by
                    have _litex_residual : (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.divValue (Litex.denote _value_i14) _raw_i11)) _captured_input)) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i15 : M.Value) => (¬ (_raw_i15 = (M.number (0 : ℂ))))) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i15 : M.Value) => (M.divValue (Litex.denote _value_i14) _raw_i15)) _captured_input)) := (let _equal_wd_2_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) (fun (_raw_i11 : M.Value) => (M.divValue (Litex.denote _value_i14) _raw_i11)) (by
                      intro _raw_i11 h_1784 h_1733
                      let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_1784)
                      have h_1784 : Litex.In _value_i11 (Litex.R (M := M)) := h_1784
                      have h_1733 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (¬ (_raw_i11 = (M.number (0 : ℂ))))
                                exact h_1733)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (Litex.div _value_i14 _value_i11 (M.real_subset_complex _ h_1548) (M.real_subset_complex _ h_1784) h_1733)
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.div _value_i14 _value_i11 (M.real_subset_complex _ h_1548) (M.real_subset_complex _ h_1784) h_1733)
                        exact (Litex.divInR _value_i14 _value_i11 h_1548 h_1784 (_atomic_wd_1_0).wd.2.2))));
                    let _equal_wd_2_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i15 : M.Value) => (¬ (_raw_i15 = (M.number (0 : ℂ))))) (fun (_raw_i15 : M.Value) => (M.divValue (Litex.denote _value_i14) _raw_i15)) (by
                      intro _raw_i15 h_1937 h_1532
                      let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_1937)
                      have h_1937 : Litex.In _value_i15 (Litex.R (M := M)) := h_1937
                      have h_1532 : ¬ Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (¬ (_raw_i15 = (M.number (0 : ℂ))))
                                exact h_1532)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (Litex.div _value_i14 _value_i15 (M.real_subset_complex _ h_1548) (M.real_subset_complex _ h_1937) h_1532)
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.div _value_i14 _value_i15 (M.real_subset_complex _ h_1548) (M.real_subset_complex _ h_1937) h_1532)
                        exact (Litex.divInR _value_i14 _value_i15 h_1548 h_1937 (_atomic_wd_1_0).wd.2.2))));
                    (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (by
                      let _left : Litex.Obj (M := M) (Litex.FormulaFn M) := _equal_wd_2_0
                      let _right : Litex.Obj (M := M) (Litex.FormulaFn M) := _equal_wd_2_1
                      exact (show Litex.Same _left _right from rfl))))
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i14)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i14)) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.divValue (Litex.denote _value_i14) _raw_i11)) _captured_input)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i8 (M := M));
                  let _wd_1_1 := _value_i14;
                  (let _litex_call_arg_0 := _wd_1_1;
                  Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))) _raw_i10) → True := (by
                      intro _raw_i10 h_1529 h_1223
                      let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_1529)
                      have h_1529 : Litex.In _value_i10 (Litex.R (M := M)) := h_1529
                      have h_1223 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (¬ (_raw_i10 = (M.number (0 : ℂ))))
                                exact h_1223)
                            )
                        )
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) h_1548 True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_1531 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.divValue _raw_i9 _raw_i11)) _captured_input))) _litex_input) (Litex.denote _litex_literal.val.argument) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.divValue (Litex.denote _value_i14) _raw_i11)) _captured_input)); exact rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w31 := (by
            let _returned_receiver := (let _litex_call_arg_0 := _value_i14;
          Litex.callOn ((_object_i8 (M := M))).val.signature (_object_i8 (M := M)) _litex_call_arg_0 (h_1530 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_1548, True.intro⟩))
            let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))))
            have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
            have _returned_domain : M.mem (Litex.denote (Litex.number (M := M) (2 : ℂ))) _returned_signature.domain := ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))⟩)
            exact Litex.callOn _returned_signature _returned_receiver (Litex.number (M := M) (2 : ℂ)) _returned_member _returned_domain)
          let _object_w32 := (Litex.div _value_i14 (Litex.number (M := M) (2 : ℂ)) (M.real_subset_complex _ h_1548) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
          have h_1534 : (by
            let _equal_wd_1_0 := _object_w31
            let _equal_wd_1_1 := _object_w32
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i14)) (M.number (2 : ℂ))) = (M.divValue (Litex.denote _value_i14) (M.number (2 : ℂ))) from by
                    have _litex_residual : (M.divValue (Litex.denote _value_i14) (M.number (2 : ℂ))) = (M.divValue (Litex.denote _value_i14) (M.number (2 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i14)) (M.number (2 : ℂ))))).trans (congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (M.number (2 : ℂ))) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.denote _value_i14)) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.divValue (Litex.denote _value_i14) _raw_i11)) _captured_input)) from by
                    let _litex_original := _object_w27
                    let _litex_literal := (let _wd_1_0 := (_object_i8 (M := M));
                  let _wd_1_1 := _value_i14;
                  (let _litex_call_arg_0 := _wd_1_1;
                  Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))) _raw_i10) → True := (by
                      intro _raw_i10 h_1529 h_1223
                      let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_1529)
                      have h_1529 : Litex.In _value_i10 (Litex.R (M := M)) := h_1529
                      have h_1223 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (¬ (_raw_i10 = (M.number (0 : ℂ))))
                                exact h_1223)
                            )
                        )
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) => (¬ (_raw_i10 = (M.number (0 : ℂ))))))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) h_1548 True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_1531 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.divValue _raw_i9 _raw_i11)) _captured_input))) _litex_input) (Litex.denote _litex_literal.val.argument) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.divValue (Litex.denote _value_i14) _raw_i11)) _captured_input)); exact rfl))
                  )))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i11 : M.Value) => (M.divValue (Litex.denote _value_i14) _raw_i11)) _captured_input)) (M.number (2 : ℂ))) = (M.divValue (Litex.denote _value_i14) (M.number (2 : ℂ))) from by
                    let _litex_original := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) (fun (_raw_i11 : M.Value) => (M.divValue (Litex.denote _value_i14) _raw_i11)) (by
                      intro _raw_i11 h_2410 h_2365
                      let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_2410)
                      have h_2410 : Litex.In _value_i11 (Litex.R (M := M)) := h_2410
                      have h_2365 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (¬ (_raw_i11 = (M.number (0 : ℂ))))
                                exact h_2365)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (Litex.div _value_i14 _value_i11 (M.real_subset_complex _ h_1548) (M.real_subset_complex _ h_2410) h_2365)
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.div _value_i14 _value_i11 (M.real_subset_complex _ h_1548) (M.real_subset_complex _ h_2410) h_2365)
                        exact (Litex.divInR _value_i14 _value_i11 h_1548 h_2410 (_atomic_wd_1_0).wd.2.2))));
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
                    let _litex_literal := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) (fun (_raw_i11 : M.Value) => (M.divValue (Litex.denote _value_i14) _raw_i11)) (by
                      intro _raw_i11 h_2571 h_2365
                      let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_2571)
                      have h_2571 : Litex.In _value_i11 (Litex.R (M := M)) := h_2571
                      have h_2365 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (by
                                change (¬ (_raw_i11 = (M.number (0 : ℂ))))
                                exact h_2365)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (Litex.div _value_i14 _value_i11 (M.real_subset_complex _ h_1548) (M.real_subset_complex _ h_2571) h_2365)
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.div _value_i14 _value_i11 (M.real_subset_complex _ h_1548) (M.real_subset_complex _ h_2571) h_2365)
                        exact (Litex.divInR _value_i14 _value_i11 h_1548 h_2571 (_atomic_wd_1_0).wd.2.2))));
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) (fun (_raw_i11 : M.Value) => (M.divValue (Litex.denote _value_i14) _raw_i11)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i11 : M.Value) => (M.divValue (Litex.denote _value_i14) _raw_i11)) (Litex.denote _litex_literal.val.argument) = (M.divValue (Litex.denote _value_i14) (M.number (2 : ℂ))) from rfl))
                  ))).trans _litex_residual)
                )
            )
          exact (And.intro h_1533 h_1534)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_captured_x5f_division_x5f_functions_x2f_statement_x2e_lit
