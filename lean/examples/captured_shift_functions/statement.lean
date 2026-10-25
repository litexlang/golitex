import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_captured_x5f_shift_x5f_functions_x2f_statement_x2e_lit

universe u v5 v11
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFnOn (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_15 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_15)
    have h_15 : Litex.In _value_i3 (Litex.R (M := M)) := h_15
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 _raw_i2)) _captured_input))) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → M.mem ((fun (_raw_i2 : M.Value) => (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 _raw_i2)) _captured_input))) _raw_i2) (Litex.denote (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_15 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_15)
    have h_15 : Litex.In _value_i3 (Litex.R (M := M)) := h_15
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))) := (by
    intro _raw_i2 h_14 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
    have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
    change (by
      let _atomic_wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (Litex.denote _value_i2))) (by
        intro _raw_i4 h_115 _
        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_115)
        have h_115 : Litex.In _value_i4 (Litex.R (M := M)) := h_115
        change (by
          let _atomic_wd_2_0 := (Litex.add _value_i4 _value_i2 (M.real_subset_complex _ h_115) (M.real_subset_complex _ h_14))
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (Litex.add _value_i4 _value_i2 (M.real_subset_complex _ h_115) (M.real_subset_complex _ h_14))
          exact (Litex.addInR _value_i4 _value_i2 h_115 h_14))))
      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
          intro _raw_i3 h_187 _
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_187)
          have h_187 : Litex.In _value_i3 (Litex.R (M := M)) := h_187
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
      exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
    exact (by
      let _atomic_wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (Litex.denote _value_i2))) (by
        intro _raw_i4 h_115 _
        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_115)
        have h_115 : Litex.In _value_i4 (Litex.R (M := M)) := h_115
        change (by
          let _atomic_wd_2_0 := (Litex.add _value_i4 _value_i2 (M.real_subset_complex _ h_115) (M.real_subset_complex _ h_14))
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (Litex.add _value_i4 _value_i2 (M.real_subset_complex _ h_115) (M.real_subset_complex _ h_14))
          exact (Litex.addInR _value_i4 _value_i2 h_115 h_14))))
      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
          intro _raw_i3 h_187 _
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_187)
          have h_187 : Litex.In _value_i3 (Litex.R (M := M)) := h_187
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
      exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from by exact Litex.formulaFnInFnSet _atomic_wd_1_0)))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.R (M := M))) (Litex.denote (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_15 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_15)
    have h_15 : Litex.In _value_i3 (Litex.R (M := M)) := h_15
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))) (Litex.isSet (Litex.R (M := M))) (Litex.isSet (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_15 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_15)
    have h_15 : Litex.In _value_i3 (Litex.R (M := M)) := h_15
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_194 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_195 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_198 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_211 : Litex.In _value_i5 (Litex.R (M := M))), (by
  let _object_w6 := (let _litex_call_arg_0 := _value_i5;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_194 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_211, True.intro⟩))
  let _object_w7 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (M.addValue _raw_i6 (Litex.denote _value_i5))) (by
    intro _raw_i6 h_230 _
    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_230)
    have h_230 : Litex.In _value_i6 (Litex.R (M := M)) := h_230
    change (by
      let _atomic_wd_1_0 := (Litex.add _value_i6 _value_i5 (M.real_subset_complex _ h_230) (M.real_subset_complex _ h_211))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.add _value_i6 _value_i5 (M.real_subset_complex _ h_230) (M.real_subset_complex _ h_211))
      exact (Litex.addInR _value_i6 _value_i5 h_230 h_211))))
  let _object_w8 := (by
    let _returned_receiver := (let _litex_call_arg_0 := _value_i5;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_194 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_211, True.intro⟩))
    let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))
    have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
    have _returned_domain : M.mem (Litex.denote (Litex.number (M := M) (2 : ℂ))) _returned_signature.domain := ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), True.intro⟩)
    exact Litex.callOn _returned_signature _returned_receiver (Litex.number (M := M) (2 : ℂ)) _returned_member _returned_domain)
  let _object_w9 := (Litex.add (Litex.number (M := M) (2 : ℂ)) _value_i5 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_211))
  exact (((by
    let _equal_wd_1_0 := _object_w6
    let _equal_wd_1_1 := _object_w7
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w8
    let _equal_wd_1_1 := _object_w9
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_211
          let _object_w6 := (let _litex_call_arg_0 := _value_i5;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_194 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_211, True.intro⟩))
          let _object_w7 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (M.addValue _raw_i6 (Litex.denote _value_i5))) (by
            intro _raw_i6 h_230 _
            let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_230)
            have h_230 : Litex.In _value_i6 (Litex.R (M := M)) := h_230
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i6 _value_i5 (M.real_subset_complex _ h_230) (M.real_subset_complex _ h_211))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i6 _value_i5 (M.real_subset_complex _ h_230) (M.real_subset_complex _ h_211))
              exact (Litex.addInR _value_i6 _value_i5 h_230 h_211))))
          have h_196 : (by
            let _equal_wd_1_0 := _object_w6
            let _equal_wd_1_1 := _object_w7
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w6;
                  let _equal_wd_1_1 := _object_w7;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.addValue _raw_i6 (Litex.denote _value_i5))) _captured_input)) from by
                    have _litex_residual : (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (Litex.denote _value_i5))) _captured_input)) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.addValue _raw_i6 (Litex.denote _value_i5))) _captured_input)) := (let _equal_wd_2_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (Litex.denote _value_i5))) (by
                      intro _raw_i4 h_361 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_361)
                      have h_361 : Litex.In _value_i4 (Litex.R (M := M)) := h_361
                      change (by
                        let _atomic_wd_1_0 := (Litex.add _value_i4 _value_i5 (M.real_subset_complex _ h_361) (M.real_subset_complex _ h_211))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.add _value_i4 _value_i5 (M.real_subset_complex _ h_361) (M.real_subset_complex _ h_211))
                        exact (Litex.addInR _value_i4 _value_i5 h_361 h_211))));
                    let _equal_wd_2_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (fun (_raw_i6 : M.Value) => (M.addValue _raw_i6 (Litex.denote _value_i5))) (by
                      intro _raw_i6 h_461 _
                      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_461)
                      have h_461 : Litex.In _value_i6 (Litex.R (M := M)) := h_461
                      change (by
                        let _atomic_wd_1_0 := (Litex.add _value_i6 _value_i5 (M.real_subset_complex _ h_461) (M.real_subset_complex _ h_211))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.add _value_i6 _value_i5 (M.real_subset_complex _ h_461) (M.real_subset_complex _ h_211))
                        exact (Litex.addInR _value_i6 _value_i5 h_461 h_211))));
                    (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (by
                      let _left : Litex.Obj (M := M) (Litex.FormulaFn M) := _equal_wd_2_0
                      let _right : Litex.Obj (M := M) (Litex.FormulaFn M) := _equal_wd_2_1
                      exact (show Litex.Same _left _right from rfl))))
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (Litex.denote _value_i5))) _captured_input)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                  let _wd_1_1 := _value_i5;
                  (let _litex_call_arg_0 := _wd_1_1;
                  Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                      intro _raw_i3 h_193 _
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_193)
                      have h_193 : Litex.In _value_i3 (Litex.R (M := M)) := h_193
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) h_211 True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_195 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 _raw_i2)) _captured_input))) _litex_input) (Litex.denote _litex_literal.val.argument) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (Litex.denote _value_i5))) _captured_input)); exact rfl))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w8 := (by
            let _returned_receiver := (let _litex_call_arg_0 := _value_i5;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_194 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_211, True.intro⟩))
            let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))
            have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
            have _returned_domain : M.mem (Litex.denote (Litex.number (M := M) (2 : ℂ))) _returned_signature.domain := ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), True.intro⟩)
            exact Litex.callOn _returned_signature _returned_receiver (Litex.number (M := M) (2 : ℂ)) _returned_member _returned_domain)
          let _object_w9 := (Litex.add (Litex.number (M := M) (2 : ℂ)) _value_i5 (Litex.numberInC (M := M) (2 : ℂ)) (M.real_subset_complex _ h_211))
          have h_197 : (by
            let _equal_wd_1_0 := _object_w8
            let _equal_wd_1_1 := _object_w9
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)) (M.number (2 : ℂ))) = (M.addValue (M.number (2 : ℂ)) (Litex.denote _value_i5)) from by
                    have _litex_residual : (M.addValue (M.number (2 : ℂ)) (Litex.denote _value_i5)) = (M.addValue (M.number (2 : ℂ)) (Litex.denote _value_i5)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)) (M.number (2 : ℂ))))).trans (congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (M.number (2 : ℂ))) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (Litex.denote _value_i5))) _captured_input)) from by
                    let _litex_original := _object_w6
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                  let _wd_1_1 := _value_i5;
                  (let _litex_call_arg_0 := _wd_1_1;
                  Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                      intro _raw_i3 h_193 _
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_193)
                      have h_193 : Litex.In _value_i3 (Litex.R (M := M)) := h_193
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) h_211 True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_195 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 _raw_i2)) _captured_input))) _litex_input) (Litex.denote _litex_literal.val.argument) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (Litex.denote _value_i5))) _captured_input)); exact rfl))
                  )))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (Litex.denote _value_i5))) _captured_input)) (M.number (2 : ℂ))) = (M.addValue (M.number (2 : ℂ)) (Litex.denote _value_i5)) from by
                    let _litex_original := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (Litex.denote _value_i5))) (by
                      intro _raw_i4 h_653 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_653)
                      have h_653 : Litex.In _value_i4 (Litex.R (M := M)) := h_653
                      change (by
                        let _atomic_wd_1_0 := (Litex.add _value_i4 _value_i5 (M.real_subset_complex _ h_653) (M.real_subset_complex _ h_211))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.add _value_i4 _value_i5 (M.real_subset_complex _ h_653) (M.real_subset_complex _ h_211))
                        exact (Litex.addInR _value_i4 _value_i5 h_653 h_211))));
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro))
                    let _litex_literal := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (Litex.denote _value_i5))) (by
                      intro _raw_i4 h_758 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_758)
                      have h_758 : Litex.In _value_i4 (Litex.R (M := M)) := h_758
                      change (by
                        let _atomic_wd_1_0 := (Litex.add _value_i4 _value_i5 (M.real_subset_complex _ h_758) (M.real_subset_complex _ h_211))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.add _value_i4 _value_i5 (M.real_subset_complex _ h_758) (M.real_subset_complex _ h_211))
                        exact (Litex.addInR _value_i4 _value_i5 h_758 h_211))));
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (Litex.denote _value_i5))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (Litex.denote _value_i5))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.number (2 : ℂ)) (Litex.denote _value_i5)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          exact (And.intro h_196 h_197)
        )
      )
  )

noncomputable def _object_i7 := (Litex.formulaFnOn (let _litex_output := (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)) _raw_i9) → True := (by
    intro _raw_i9 h_906 _positive_i9
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_906)
    have h_906 : Litex.In _value_i9 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i9).mpr ⟨h_906, _positive_i9⟩)
    have h_907 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i9 h_906)
          )
      )
    have h_908 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i9 h_907)
          )
      )
    have h_909 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i9 h_907) _litex_zero.symm)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.RPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.RPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i10)) _captured_input)) (Litex.positiveReal (M := M)) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.addValue _raw_i10 _raw_i8)) _captured_input))) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (Litex.denote (Litex.RPos (M := M))) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → M.mem ((fun (_raw_i8 : M.Value) => (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i10)) _captured_input)) (Litex.positiveReal (M := M)) (fun (_captured_input : M.Value) => (fun (_raw_i10 : M.Value) => (M.addValue _raw_i10 _raw_i8)) _captured_input))) _raw_i8) (Litex.denote (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)) _raw_i9) → True := (by
    intro _raw_i9 h_906 _positive_i9
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_906)
    have h_906 : Litex.In _value_i9 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i9).mpr ⟨h_906, _positive_i9⟩)
    have h_907 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i9 h_906)
          )
      )
    have h_908 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i9 h_907)
          )
      )
    have h_909 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i9 h_907) _litex_zero.symm)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9))))) := (by
    intro _raw_i8 h_902 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_902)
    have h_902 : Litex.In _value_i8 (Litex.RPos (M := M)) := h_902
    have h_903 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i8 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i8 h_902)
          )
      )
    have h_904 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i8 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i8 h_903)
          )
      )
    have h_905 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i8 h_903) _litex_zero.symm)
          )
      )
    change (by
      let _atomic_wd_1_0 := (Litex.formulaFnTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i10 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i10)) (fun (_raw_i10 : M.Value) => (M.addValue _raw_i10 (Litex.denote _value_i8))) (by
        intro _raw_i10 h_1460 _positive_i10
        let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_1460)
        have h_1460 : Litex.In _value_i10 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i10).mpr ⟨h_1460, _positive_i10⟩)
        have h_1461 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inRPos_positive _value_i10 h_1460)
              )
          )
        have h_1462 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.ltToLe (Litex.number (M := M) 0) _value_i10 h_1461)
              )
          )
        have h_1463 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
          (by
            litex_checked_step =>
              exact (
                (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i10 h_1461) _litex_zero.symm)
              )
          )
        change (by
          let _atomic_wd_2_0 := (Litex.add _value_i10 _value_i8 (Litex.positiveRealToComplex _value_i10 h_1460) (Litex.positiveRealToComplex _value_i8 h_902))
          exact Litex.In _atomic_wd_2_0 (Litex.RPos (M := M)))
        exact (by
          let _atomic_wd_2_0 := (Litex.add _value_i10 _value_i8 (Litex.positiveRealToComplex _value_i10 h_1460) (Litex.positiveRealToComplex _value_i8 h_902))
          exact (Litex.inRPos_intro _atomic_wd_2_0 (by
            let _atomic_wd_3_0 := _atomic_wd_2_0
            exact (Litex.addInR _value_i10 _value_i8 (Litex.inRPos_real _value_i10 h_1460) (Litex.inRPos_real _value_i8 h_902))) (by
            let _atomic_wd_3_1 := _atomic_wd_2_0
            exact (by
              let _litex_positive_result := _atomic_wd_3_1
              exact Litex.addPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 h_1461 h_903
            ))))))
      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)) _raw_i9) → True := (by
          intro _raw_i9 h_1981 _positive_i9
          let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_1981)
          have h_1981 : Litex.In _value_i9 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i9).mpr ⟨h_1981, _positive_i9⟩)
          have h_1982 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i9 h_1981)
                )
            )
          have h_1983 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i9 h_1982)
                )
            )
          have h_1984 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i9 h_1982) _litex_zero.symm)
                )
            )
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9))))
      exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
    exact (by
      let _atomic_wd_1_0 := (Litex.formulaFnTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i10 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i10)) (fun (_raw_i10 : M.Value) => (M.addValue _raw_i10 (Litex.denote _value_i8))) (by
        intro _raw_i10 h_1460 _positive_i10
        let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_1460)
        have h_1460 : Litex.In _value_i10 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i10).mpr ⟨h_1460, _positive_i10⟩)
        have h_1461 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inRPos_positive _value_i10 h_1460)
              )
          )
        have h_1462 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.ltToLe (Litex.number (M := M) 0) _value_i10 h_1461)
              )
          )
        have h_1463 : ¬ Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) :=
          (by
            litex_checked_step =>
              exact (
                (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i10 h_1461) _litex_zero.symm)
              )
          )
        change (by
          let _atomic_wd_2_0 := (Litex.add _value_i10 _value_i8 (Litex.positiveRealToComplex _value_i10 h_1460) (Litex.positiveRealToComplex _value_i8 h_902))
          exact Litex.In _atomic_wd_2_0 (Litex.RPos (M := M)))
        exact (by
          let _atomic_wd_2_0 := (Litex.add _value_i10 _value_i8 (Litex.positiveRealToComplex _value_i10 h_1460) (Litex.positiveRealToComplex _value_i8 h_902))
          exact (Litex.inRPos_intro _atomic_wd_2_0 (by
            let _atomic_wd_3_0 := _atomic_wd_2_0
            exact (Litex.addInR _value_i10 _value_i8 (Litex.inRPos_real _value_i10 h_1460) (Litex.inRPos_real _value_i8 h_902))) (by
            let _atomic_wd_3_1 := _atomic_wd_2_0
            exact (by
              let _litex_positive_result := _atomic_wd_3_1
              exact Litex.addPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 h_1461 h_903
            ))))))
      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)) _raw_i9) → True := (by
          intro _raw_i9 h_1981 _positive_i9
          let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_1981)
          have h_1981 : Litex.In _value_i9 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i9).mpr ⟨h_1981, _positive_i9⟩)
          have h_1982 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i9 h_1981)
                )
            )
          have h_1983 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i9 h_1982)
                )
            )
          have h_1984 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i9 h_1982) _litex_zero.symm)
                )
            )
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9))))
      exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from by exact Litex.formulaFnInFnSet _atomic_wd_1_0)))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.RPos (M := M))) (Litex.denote (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)) _raw_i9) → True := (by
    intro _raw_i9 h_906 _positive_i9
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_906)
    have h_906 : Litex.In _value_i9 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i9).mpr ⟨h_906, _positive_i9⟩)
    have h_907 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i9 h_906)
          )
      )
    have h_908 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i9 h_907)
          )
      )
    have h_909 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i9 h_907) _litex_zero.symm)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9))))) (Litex.isSet (Litex.RPos (M := M))) (Litex.isSet (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)) _raw_i9) → True := (by
    intro _raw_i9 h_906 _positive_i9
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_906)
    have h_906 : Litex.In _value_i9 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i9).mpr ⟨h_906, _positive_i9⟩)
    have h_907 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRPos_positive _value_i9 h_906)
          )
      )
    have h_908 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i9 h_907)
          )
      )
    have h_909 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i9 h_907) _litex_zero.symm)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9))))) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_2001 : Litex.In (_object_i7 (M := M)) (Litex.fnSet ((_object_i7 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i7 (M := M)))
      )
  )
theorem h_2002 : Litex.Same (_object_i7 (M := M)) (_object_i7 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i7 (M := M)))
      )
  )

theorem h_2005 : ∀ {_Host_i11 : Type v11} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_2018 : Litex.In _value_i11 (Litex.RPos (M := M))), (by
  let _object_w18 := (let _litex_call_arg_0 := _value_i11;
  Litex.callOn ((_object_i7 (M := M))).val.signature (_object_i7 (M := M)) _litex_call_arg_0 (h_2001 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_2018, True.intro⟩))
  let _object_w19 := (let _checked_header : ∀ (_raw_i12 : M.Value), M.mem _raw_i12 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i12 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i12)) _raw_i12) → True := (by
      intro _raw_i12 h_2027 _positive_i12
      let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_2027)
      have h_2027 : Litex.In _value_i12 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i12).mpr ⟨h_2027, _positive_i12⟩)
      have h_2028 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i12 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inRPos_positive _value_i12 h_2027)
            )
        )
      have h_2029 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i12 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.ltToLe (Litex.number (M := M) 0) _value_i12 h_2028)
            )
        )
      have h_2030 : ¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i12 h_2028) _litex_zero.symm)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i12 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i12))))
  let _object_w20 := (by
    let _returned_receiver := (let _litex_call_arg_0 := _value_i11;
  Litex.callOn ((_object_i7 (M := M))).val.signature (_object_i7 (M := M)) _litex_call_arg_0 (h_2001 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_2018, True.intro⟩))
    let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)))
    have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
    have _returned_domain : M.mem (Litex.denote (Litex.number (M := M) (1 : ℂ))) _returned_signature.domain := ((Litex.FunctionSignature.oneTarget_domain Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)) (Litex.denote (Litex.number (M := M) (1 : ℂ)))).mpr ⟨(Litex.inRPos_real (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num) (by norm_num)))), ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (1 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num) (by norm_num)))).2⟩)
    exact Litex.callOn _returned_signature _returned_receiver (Litex.number (M := M) (1 : ℂ)) _returned_member _returned_domain)
  exact (((by
    let _atomic_wd_1_0 := _object_w18
    let _atomic_wd_1_1 := _object_w19
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)) ∧ ((by
    let _atomic_wd_1_0 := _object_w20
    exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i11 _rep_i11 _value_i11 h_2018
          have h_2019 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i11 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i11 h_2018)
                )
            )
          have h_2020 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i11 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i11 h_2019)
                )
            )
          have h_2021 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i11 h_2019) _litex_zero.symm)
                )
            )
          let _object_w18 := (let _litex_call_arg_0 := _value_i11;
          Litex.callOn ((_object_i7 (M := M))).val.signature (_object_i7 (M := M)) _litex_call_arg_0 (h_2001 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_2018, True.intro⟩))
          let _object_w19 := (let _checked_header : ∀ (_raw_i12 : M.Value), M.mem _raw_i12 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i12 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i12)) _raw_i12) → True := (by
              intro _raw_i12 h_2027 _positive_i12
              let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_2027)
              have h_2027 : Litex.In _value_i12 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i12).mpr ⟨h_2027, _positive_i12⟩)
              have h_2028 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i12 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inRPos_positive _value_i12 h_2027)
                    )
                )
              have h_2029 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i12 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.ltToLe (Litex.number (M := M) 0) _value_i12 h_2028)
                    )
                )
              have h_2030 : ¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i12 h_2028) _litex_zero.symm)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i12 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i12))))
          have h_2003 : (by
            let _atomic_wd_1_0 := _object_w18
            let _atomic_wd_1_1 := _object_w19
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w18
                    let _atomic_wd_1_1 := _object_w19
                    exact (by
                      let _litex_return_call := _atomic_wd_1_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)) _raw_i9) → True := (by
                        intro _raw_i9 h_1997 _positive_i9
                        let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_1997)
                        have h_1997 : Litex.In _value_i9 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i9).mpr ⟨h_1997, _positive_i9⟩)
                        have h_1998 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRPos_positive _value_i9 h_1997)
                              )
                          )
                        have h_1999 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.ltToLe (Litex.number (M := M) 0) _value_i9 h_1998)
                              )
                          )
                        have h_2000 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i9 h_1998) _litex_zero.symm)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)))) _atomic_wd_1_1 (Litex.sameRefl _litex_return_call) (by
                      let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)) _raw_i9) → True := (by
                        intro _raw_i9 h_1997 _positive_i9
                        let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_1997)
                        have h_1997 : Litex.In _value_i9 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i9).mpr ⟨h_1997, _positive_i9⟩)
                        have h_1998 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inRPos_positive _value_i9 h_1997)
                              )
                          )
                        have h_1999 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.ltToLe (Litex.number (M := M) 0) _value_i9 h_1998)
                              )
                          )
                        have h_2000 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i9 h_1998) _litex_zero.symm)
                              )
                          )
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9))))
                      let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_1_1
                      exact (show Litex.Same _left _right from rfl)) (Litex.callOnInOutput _litex_return_call)))
                )
            )
          let _object_w20 := (by
            let _returned_receiver := (let _litex_call_arg_0 := _value_i11;
          Litex.callOn ((_object_i7 (M := M))).val.signature (_object_i7 (M := M)) _litex_call_arg_0 (h_2001 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_2018, True.intro⟩))
            let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.oneTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)))
            have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
            have _returned_domain : M.mem (Litex.denote (Litex.number (M := M) (1 : ℂ))) _returned_signature.domain := ((Litex.FunctionSignature.oneTarget_domain Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i9 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i9)) (Litex.denote (Litex.number (M := M) (1 : ℂ)))).mpr ⟨(Litex.inRPos_real (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num) (by norm_num)))), ((Litex.positiveReal_members (M := M) (Litex.denote (Litex.number (M := M) (1 : ℂ)))).mp (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.RPos (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInRPosOfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num) (by norm_num)))).2⟩)
            exact Litex.callOn _returned_signature _returned_receiver (Litex.number (M := M) (1 : ℂ)) _returned_member _returned_domain)
          have h_2004 : (by
            let _atomic_wd_1_0 := _object_w20
            exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w20
                    exact (by
                      let _litex_return_call := _atomic_wd_1_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callOnInOutput _litex_return_call)))
                )
            )
          have h_2102 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _object_w20 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _object_w20 h_2004)
                )
            )
          have h_2103 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _object_w20 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _object_w20 h_2102)
                )
            )
          have h_2104 : ¬ Litex.Same _object_w20 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _object_w20 h_2102) _litex_zero.symm)
                )
            )
          exact (And.intro h_2003 h_2004)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_captured_x5f_shift_x5f_functions_x2f_statement_x2e_lit
