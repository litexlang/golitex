import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_selected_x5f_shift_x5f_function_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFnOn (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_15 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_15)
    have h_15 : Litex.In _value_i3 (Litex.R (M := M)) := h_15
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.denote (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (M.number (1 : ℂ)))) (by
  intro _raw_i4 h_29 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_29)
  have h_29 : Litex.In _value_i4 (Litex.R (M := M)) := h_29
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i4 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_29) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i4 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_29) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInR _value_i4 (Litex.number (M := M) (1 : ℂ)) h_29 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))))))) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → M.mem ((fun (_raw_i2 : M.Value) => (Litex.denote (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (M.number (1 : ℂ)))) (by
  intro _raw_i4 h_29 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_29)
  have h_29 : Litex.In _value_i4 (Litex.R (M := M)) := h_29
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i4 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_29) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i4 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_29) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInR _value_i4 (Litex.number (M := M) (1 : ℂ)) h_29 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))))))) _raw_i2) (Litex.denote (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_15 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_15)
    have h_15 : Litex.In _value_i3 (Litex.R (M := M)) := h_15
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))) := (by
    intro _raw_i2 h_14 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
    have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
    change (by
      let _atomic_wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (M.number (1 : ℂ)))) (by
        intro _raw_i4 h_96 _
        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_96)
        have h_96 : Litex.In _value_i4 (Litex.R (M := M)) := h_96
        change (by
          let _atomic_wd_2_0 := (Litex.add _value_i4 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_96) (Litex.numberInC (M := M) (1 : ℂ)))
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (Litex.add _value_i4 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_96) (Litex.numberInC (M := M) (1 : ℂ)))
          exact (Litex.addInR _value_i4 (Litex.number (M := M) (1 : ℂ)) h_96 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))))
      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
          intro _raw_i3 h_149 _
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_149)
          have h_149 : Litex.In _value_i3 (Litex.R (M := M)) := h_149
          exact True.intro);
        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
      exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
    exact (by
      let _atomic_wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (M.number (1 : ℂ)))) (by
        intro _raw_i4 h_96 _
        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_96)
        have h_96 : Litex.In _value_i4 (Litex.R (M := M)) := h_96
        change (by
          let _atomic_wd_2_0 := (Litex.add _value_i4 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_96) (Litex.numberInC (M := M) (1 : ℂ)))
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (Litex.add _value_i4 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_96) (Litex.numberInC (M := M) (1 : ℂ)))
          exact (Litex.addInR _value_i4 (Litex.number (M := M) (1 : ℂ)) h_96 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))))
      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
          intro _raw_i3 h_149 _
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_149)
          have h_149 : Litex.In _value_i3 (Litex.R (M := M)) := h_149
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
theorem h_156 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_157 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_i5 := (let _litex_call_arg_0 := (Litex.number (M := M) (0 : ℂ));
Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_156 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)), True.intro⟩))
theorem h_161 : Litex.Same (_object_i5 (M := M)) (let _litex_call_arg_0 := (Litex.number (M := M) (0 : ℂ));
Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_156 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)), True.intro⟩)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (let _litex_call_arg_0 := (Litex.number (M := M) (0 : ℂ));
        Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_156 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)), True.intro⟩)))
      )
  )

noncomputable def _object_w10 := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
    intro _raw_i6 h_163 _
    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_163)
    have h_163 : Litex.In _value_i6 (Litex.R (M := M)) := h_163
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)))

theorem h_162 : (by
  let _atomic_wd_1_1 := (_object_w10 (M := M))
  exact Litex.In (_object_i5 (M := M)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_1 := (_object_w10 (M := M))
          exact (Litex.inOfSame (let _litex_call_arg_0 := (Litex.number (M := M) (0 : ℂ));
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_156 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)), True.intro⟩)) (_object_i5 (M := M)) _atomic_wd_1_1 _atomic_wd_1_1 ((((Litex.sameRefl (_object_i5 (M := M)))).trans (h_161 (M := M)))).symm (Litex.sameRefl _atomic_wd_1_1) (by
            let _atomic_wd_2_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (0 : ℂ));
            Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_156 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)), True.intro⟩))
            let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := (by
                intro _raw_i6 h_191 _
                let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_191)
                have h_191 : Litex.In _value_i6 (Litex.R (M := M)) := h_191
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True)))
            exact (by
              let _litex_return_call := (let _litex_call_arg_0 := (Litex.number (M := M) (0 : ℂ));
            Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_156 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)), True.intro⟩))
              exact Litex.inOfSame _litex_return_call _litex_return_call (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                intro _raw_i3 h_155 _
                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_155)
                have h_155 : Litex.In _value_i3 (Litex.R (M := M)) := h_155
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) _atomic_wd_2_1 (Litex.sameRefl _litex_return_call) (by
              let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                intro _raw_i3 h_155 _
                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_155)
                have h_155 : Litex.In _value_i3 (Litex.R (M := M)) := h_155
                exact True.intro);
              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
              let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
              exact (show Litex.Same _left _right from rfl)) (Litex.callOnInOutput _litex_return_call)))))
      )
  )

noncomputable def _object_w11 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True) (_object_i5 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_162 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro)

theorem h_199 : (by
  let _atomic_wd_1_0 := (_object_w11 (M := M))
  exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w11 (M := M))
          exact (by
            let _litex_return_call := _atomic_wd_1_0
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))
      )
  )

noncomputable def _object_w13 := (by
  have _range_signature_0 : Litex.In (_object_i5 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) := (by
  let _returned_signature : Litex.FunctionSignature M := (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_155 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_155)
    have h_155 : Litex.In _value_i3 (Litex.R (M := M)) := h_155
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))
  have _returned_source : Litex.In (_object_i1 (M := M)) (Litex.fnSet _returned_signature) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_155 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_155)
    have h_155 : Litex.In _value_i3 (Litex.R (M := M)) := h_155
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_155 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_155)
    have h_155 : Litex.In _value_i3 (Litex.R (M := M)) := h_155
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (Litex.sameRefl (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_155 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_155)
    have h_155 : Litex.In _value_i3 (Litex.R (M := M)) := h_155
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)))) (h_156 (M := M)))
  have _returned_input : M.mem (Litex.denote (Litex.number (M := M) (0 : ℂ))) _returned_signature.domain := (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_155 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_155)
    have h_155 : Litex.In _value_i3 (Litex.R (M := M)) := h_155
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) (Litex.denote (Litex.number (M := M) (0 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)), True.intro⟩)
  have _returned_member : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (0 : ℂ));
Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_156 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)), True.intro⟩)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_155 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_155)
    have h_155 : Litex.In _value_i3 (Litex.R (M := M)) := h_155
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) := Litex.FunctionSemantics.call_mem _returned_signature.domain _returned_signature.output (Litex.denote (_object_i1 (M := M))) (Litex.denote (Litex.number (M := M) (0 : ℂ))) _returned_source _returned_input
  exact Litex.inOfSame (let _litex_call_arg_0 := (Litex.number (M := M) (0 : ℂ));
Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_156 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)), True.intro⟩)) (_object_i5 (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_155 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_155)
    have h_155 : Litex.In _value_i3 (Litex.R (M := M)) := h_155
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) ((h_161 (M := M))).symm (show @Eq M.Value _ _ from Eq.refl _) _returned_member)
  have _range_signature_1 : Litex.In (_object_i5 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) := (by
  let _returned_signature : Litex.FunctionSignature M := (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_155 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_155)
    have h_155 : Litex.In _value_i3 (Litex.R (M := M)) := h_155
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))
  have _returned_source : Litex.In (_object_i1 (M := M)) (Litex.fnSet _returned_signature) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_155 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_155)
    have h_155 : Litex.In _value_i3 (Litex.R (M := M)) := h_155
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_155 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_155)
    have h_155 : Litex.In _value_i3 (Litex.R (M := M)) := h_155
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) ((((h_157 (M := M))).symm).trans ((show @Eq M.Value _ _ from Eq.refl _)).symm) (Litex.sameRefl (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_155 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_155)
    have h_155 : Litex.In _value_i3 (Litex.R (M := M)) := h_155
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)))) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
  have _returned_input : M.mem (Litex.denote (Litex.number (M := M) (0 : ℂ))) _returned_signature.domain := (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_155 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_155)
    have h_155 : Litex.In _value_i3 (Litex.R (M := M)) := h_155
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) (Litex.denote (Litex.number (M := M) (0 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)), True.intro⟩)
  have _returned_member : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (0 : ℂ));
Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_156 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)), True.intro⟩)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_155 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_155)
    have h_155 : Litex.In _value_i3 (Litex.R (M := M)) := h_155
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) := Litex.FunctionSemantics.call_mem _returned_signature.domain _returned_signature.output (Litex.denote (_object_i1 (M := M))) (Litex.denote (Litex.number (M := M) (0 : ℂ))) _returned_source _returned_input
  exact Litex.inOfSame (let _litex_call_arg_0 := (Litex.number (M := M) (0 : ℂ));
Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_156 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)), True.intro⟩)) (_object_i5 (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_155 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_155)
    have h_155 : Litex.In _value_i3 (Litex.R (M := M)) := h_155
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) ((h_161 (M := M))).symm (show @Eq M.Value _ _ from Eq.refl _) _returned_member)
  have _range_signature_2 : Litex.In (_object_i5 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) := (Litex.inOfSame (_object_i5 (M := M)) (_object_i5 (M := M)) (_object_w10 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) (h_162 (M := M)))
  exact Litex.fnRange (_object_i5 (M := M)) (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)) _range_signature_0)

theorem h_256 : (by
  let _atomic_wd_1_0 := (_object_w13 (M := M))
  exact Litex.IsSet _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w13 (M := M))
          exact (Litex.isSet _atomic_wd_1_0))
      )
  )

noncomputable def _object_w14 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => (M.addValue _raw_i7 (M.number (1 : ℂ)))) (by
  intro _raw_i7 h_285 _
  let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_285)
  have h_285 : Litex.In _value_i7 (Litex.R (M := M)) := h_285
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i7 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_285) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i7 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_285) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInR _value_i7 (Litex.number (M := M) (1 : ℂ)) h_285 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))))

theorem h_271 : (by
  let _equal_wd_1_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (0 : ℂ));
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_156 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)), True.intro⟩))
  let _equal_wd_1_1 := (_object_w14 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (0 : ℂ));
        Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_156 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)), True.intro⟩));
        let _equal_wd_1_1 := (_object_w14 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (0 : ℂ))) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.addValue _raw_i7 (M.number (1 : ℂ)))) _captured_input)) from by
          have _litex_residual : (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (M.number (1 : ℂ)))) _captured_input)) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i7 : M.Value) => (M.addValue _raw_i7 (M.number (1 : ℂ)))) _captured_input)) := (let _equal_wd_2_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (M.number (1 : ℂ)))) (by
            intro _raw_i4 h_504 _
            let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_504)
            have h_504 : Litex.In _value_i4 (Litex.R (M := M)) := h_504
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i4 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_504) (Litex.numberInC (M := M) (1 : ℂ)))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i4 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_504) (Litex.numberInC (M := M) (1 : ℂ)))
              exact (Litex.addInR _value_i4 (Litex.number (M := M) (1 : ℂ)) h_504 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))));
          let _equal_wd_2_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i7 : M.Value) => True) (fun (_raw_i7 : M.Value) => (M.addValue _raw_i7 (M.number (1 : ℂ)))) (by
            intro _raw_i7 h_599 _
            let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_599)
            have h_599 : Litex.In _value_i7 (Litex.R (M := M)) := h_599
            change (by
              let _atomic_wd_1_0 := (Litex.add _value_i7 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_599) (Litex.numberInC (M := M) (1 : ℂ)))
              exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i7 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_599) (Litex.numberInC (M := M) (1 : ℂ)))
              exact (Litex.addInR _value_i7 (Litex.number (M := M) (1 : ℂ)) h_599 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))));
          (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (by
            let _left : Litex.Obj (M := M) (Litex.FormulaFn M) := _equal_wd_2_0
            let _right : Litex.Obj (M := M) (Litex.FormulaFn M) := _equal_wd_2_1
            exact (show Litex.Same _left _right from rfl))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (0 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.number (0 : ℂ))) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (M.number (1 : ℂ)))) _captured_input)) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
        let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
        (let _litex_call_arg_0 := _wd_1_1;
        Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
            intro _raw_i3 h_155 _
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_155)
            have h_155 : Litex.In _value_i3 (Litex.R (M := M)) := h_155
            exact True.intro);
          Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_157 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
          exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.denote (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (M.number (1 : ℂ)))) (by
          intro _raw_i4 h_96 _
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_96)
          have h_96 : Litex.In _value_i4 (Litex.R (M := M)) := h_96
          change (by
            let _atomic_wd_1_0 := (Litex.add _value_i4 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_96) (Litex.numberInC (M := M) (1 : ℂ)))
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.add _value_i4 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_96) (Litex.numberInC (M := M) (1 : ℂ)))
            exact (Litex.addInR _value_i4 (Litex.number (M := M) (1 : ℂ)) h_96 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))))))) _litex_input) (Litex.denote _litex_literal.val.argument) = (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _captured_input)) (M.standard Litex.StandardSetValue.real) (fun (_captured_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.addValue _raw_i4 (M.number (1 : ℂ)))) _captured_input)); exact rfl))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_w15 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True) (fun (_raw_i8 : M.Value) => (M.addValue _raw_i8 (M.number (1 : ℂ)))) (by
  intro _raw_i8 h_697 _
  let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_697)
  have h_697 : Litex.In _value_i8 (Litex.R (M := M)) := h_697
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_697) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_697) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInR _value_i8 (Litex.number (M := M) (1 : ℂ)) h_697 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))))

theorem h_683 : (by
  let _equal_wd_1_1 := (_object_w15 (M := M))
  exact Litex.Same (_object_i5 (M := M)) _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_2_0 := (_object_w14 (M := M));
        let _equal_wd_2_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True) (fun (_raw_i8 : M.Value) => (M.addValue _raw_i8 (M.number (1 : ℂ)))) (by
          intro _raw_i8 h_909 _
          let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_909)
          have h_909 : Litex.In _value_i8 (Litex.R (M := M)) := h_909
          change (by
            let _atomic_wd_1_0 := (Litex.add _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_909) (Litex.numberInC (M := M) (1 : ℂ)))
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.add _value_i8 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_909) (Litex.numberInC (M := M) (1 : ℂ)))
            exact (Litex.addInR _value_i8 (Litex.number (M := M) (1 : ℂ)) h_909 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))));
        (show Litex.Same (_object_i5 (M := M)) _equal_wd_2_1 from (Eq.trans (((h_161 (M := M))).trans (h_271 (M := M))) (Eq.trans (by
          let _left : Litex.Obj (M := M) (Litex.FormulaFn M) := _equal_wd_2_0
          let _right : Litex.Obj (M := M) (Litex.FormulaFn M) := _equal_wd_2_1
          exact (show Litex.Same _left _right from rfl)) (show @Eq M.Value _ _ from Eq.refl _)))))
      )
  )

theorem h_993 : (by
  let _equal_wd_1_0 := (_object_w11 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (M.number (2 : ℂ))) = (M.number (3 : ℂ)) from by
          have _litex_residual : (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) = (M.number (3 : ℂ)) := (let _equal_wd_2_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) ((2 : ℂ) + (1 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (M.number (2 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (M.number (2 : ℂ))) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) from by
          let _litex_original := (_object_w11 (M := M))
          let _litex_literal := (let _wd_1_0 := (_object_w15 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_683 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True) (fun (_raw_i8 : M.Value) => (M.addValue _raw_i8 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i8 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i8 : M.Value) => (M.addValue _raw_i8 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) from rfl))
        ))).trans _litex_residual)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_selected_x5f_shift_x5f_function_x2f_statement_x2e_lit
