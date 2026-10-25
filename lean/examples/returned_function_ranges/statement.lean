import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_returned_x5f_function_x5f_ranges_x2f_statement_x2e_lit

universe u v1 v4 v7 v10
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_29 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_27 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_27)
    have h_27 : Litex.In _value_i2 (Litex.R (M := M)) := h_27
    exact True.intro);
  Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_28 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
    have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)))), (by
  let _object_w9 := (let _wd_1_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
  Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_28 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
      have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_29 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro);
  (by
    have _range_signature_0 : Litex.In _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) := (by
    let _returned_signature : Litex.FunctionSignature M := (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_28 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
      have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))
    have _returned_source : Litex.In _value_i1 (Litex.fnSet _returned_signature) := (Litex.inOfSame _value_i1 _value_i1 (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_28 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
      have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_28 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
      have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (Litex.sameRefl (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_28 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
      have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)))) h_29)
    have _returned_input : M.mem (Litex.denote (Litex.number (M := M) (1 : ℂ))) _returned_signature.domain := (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_28 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
      have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) (Litex.denote (Litex.number (M := M) (1 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)), True.intro⟩)
    have _returned_member : Litex.In _wd_1_0 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_28 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
      have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) := Litex.FunctionSemantics.call_mem _returned_signature.domain _returned_signature.output (Litex.denote _value_i1) (Litex.denote (Litex.number (M := M) (1 : ℂ))) _returned_source _returned_input
    exact Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_28 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
      have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) _returned_member)
    exact Litex.fnRange _wd_1_0 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)) _range_signature_0))
  exact (by
    let _atomic_wd_1_0 := _object_w9
    exact Litex.IsSet _atomic_wd_1_0)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_29
          let _object_w9 := (let _wd_1_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
          Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_28 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
              have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_29 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro);
          (by
            have _range_signature_0 : Litex.In _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) := (by
            let _returned_signature : Litex.FunctionSignature M := (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_28 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
              have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))
            have _returned_source : Litex.In _value_i1 (Litex.fnSet _returned_signature) := (Litex.inOfSame _value_i1 _value_i1 (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_28 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
              have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_28 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
              have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (Litex.sameRefl (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_28 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
              have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)))) h_29)
            have _returned_input : M.mem (Litex.denote (Litex.number (M := M) (1 : ℂ))) _returned_signature.domain := (let _litex_output := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_28 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
              have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))); (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) (Litex.denote (Litex.number (M := M) (1 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)), True.intro⟩)
            have _returned_member : Litex.In _wd_1_0 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_28 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
              have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) := Litex.FunctionSemantics.call_mem _returned_signature.domain _returned_signature.output (Litex.denote _value_i1) (Litex.denote (Litex.number (M := M) (1 : ℂ))) _returned_source _returned_input
            exact Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_28 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
              have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) _returned_member)
            exact Litex.fnRange _wd_1_0 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)) _range_signature_0))
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w9
            exact Litex.IsSet _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w9
                    exact (Litex.isSet _atomic_wd_1_0))
                )
            )
          exact h_1
        )
      )
  )

theorem h_39 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_73 : Litex.In _value_i4 (let _checked_header : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _raw_i5) → True := (by
    intro _raw_i5 h_70 h_36
    let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_70)
    have h_70 : Litex.In _value_i5 (Litex.R (M := M)) := h_70
    have h_36 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i5 = (M.number (0 : ℂ))))
              exact h_36)
          )
      )
    exact True.intro);
  Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := (by
    intro _raw_i6 h_71 h_37
    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_71)
    have h_71 : Litex.In _value_i6 (Litex.R (M := M)) := h_71
    have h_37 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i6 = (M.number (0 : ℂ))))
              exact h_37)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _litex_input)))), (by
  let _object_w25 := (let _wd_1_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
  Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := (by
      intro _raw_i6 h_71 h_37
      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_71)
      have h_71 : Litex.In _value_i6 (Litex.R (M := M)) := h_71
      have h_37 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                exact h_37)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _litex_input) _value_i4 _litex_call_arg_0 h_73 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (by
    have _range_signature_0 : Litex.In _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))) := (by
    let _returned_signature : Litex.FunctionSignature M := (let _litex_output := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := (by
      intro _raw_i6 h_71 h_37
      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_71)
      have h_71 : Litex.In _value_i6 (Litex.R (M := M)) := h_71
      have h_37 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                exact h_37)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _litex_input))
    have _returned_source : Litex.In _value_i4 (Litex.fnSet _returned_signature) := (Litex.inOfSame _value_i4 _value_i4 (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := (by
      intro _raw_i6 h_71 h_37
      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_71)
      have h_71 : Litex.In _value_i6 (Litex.R (M := M)) := h_71
      have h_37 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                exact h_37)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _litex_input))) (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := (by
      intro _raw_i6 h_71 h_37
      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_71)
      have h_71 : Litex.In _value_i6 (Litex.R (M := M)) := h_71
      have h_37 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                exact h_37)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (Litex.sameRefl (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := (by
      intro _raw_i6 h_71 h_37
      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_71)
      have h_71 : Litex.In _value_i6 (Litex.R (M := M)) := h_71
      have h_37 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                exact h_37)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _litex_input)))) h_73)
    have _returned_input : M.mem (Litex.denote (Litex.number (M := M) (2 : ℂ))) _returned_signature.domain := (let _litex_output := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := (by
      intro _raw_i6 h_71 h_37
      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_71)
      have h_71 : Litex.In _value_i6 (Litex.R (M := M)) := h_71
      have h_37 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                exact h_37)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))); (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _litex_input) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))⟩)
    have _returned_member : Litex.In _wd_1_0 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := (by
      intro _raw_i6 h_71 h_37
      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_71)
      have h_71 : Litex.In _value_i6 (Litex.R (M := M)) := h_71
      have h_37 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                exact h_37)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))) := Litex.FunctionSemantics.call_mem _returned_signature.domain _returned_signature.output (Litex.denote _value_i4) (Litex.denote (Litex.number (M := M) (2 : ℂ))) _returned_source _returned_input
    exact Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := (by
      intro _raw_i6 h_71 h_37
      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_71)
      have h_71 : Litex.In _value_i6 (Litex.R (M := M)) := h_71
      have h_37 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          litex_checked_step =>
            exact (
              (by
                change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                exact h_37)
            )
        )
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) _returned_member)
    exact Litex.fnRange _wd_1_0 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ)))))) _range_signature_0))
  exact (by
    let _atomic_wd_1_0 := _object_w25
    exact Litex.IsSet _atomic_wd_1_0)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_73
          let _object_w25 := (let _wd_1_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
          Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := (by
              intro _raw_i6 h_71 h_37
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_71)
              have h_71 : Litex.In _value_i6 (Litex.R (M := M)) := h_71
              have h_37 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                        exact h_37)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _litex_input) _value_i4 _litex_call_arg_0 h_73 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (by
            have _range_signature_0 : Litex.In _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))) := (by
            let _returned_signature : Litex.FunctionSignature M := (let _litex_output := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := (by
              intro _raw_i6 h_71 h_37
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_71)
              have h_71 : Litex.In _value_i6 (Litex.R (M := M)) := h_71
              have h_37 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                        exact h_37)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _litex_input))
            have _returned_source : Litex.In _value_i4 (Litex.fnSet _returned_signature) := (Litex.inOfSame _value_i4 _value_i4 (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := (by
              intro _raw_i6 h_71 h_37
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_71)
              have h_71 : Litex.In _value_i6 (Litex.R (M := M)) := h_71
              have h_37 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                        exact h_37)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _litex_input))) (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := (by
              intro _raw_i6 h_71 h_37
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_71)
              have h_71 : Litex.In _value_i6 (Litex.R (M := M)) := h_71
              have h_37 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                        exact h_37)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (Litex.sameRefl (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := (by
              intro _raw_i6 h_71 h_37
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_71)
              have h_71 : Litex.In _value_i6 (Litex.R (M := M)) := h_71
              have h_37 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                        exact h_37)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _litex_input)))) h_73)
            have _returned_input : M.mem (Litex.denote (Litex.number (M := M) (2 : ℂ))) _returned_signature.domain := (let _litex_output := (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := (by
              intro _raw_i6 h_71 h_37
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_71)
              have h_71 : Litex.In _value_i6 (Litex.R (M := M)) := h_71
              have h_37 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                        exact h_37)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))); (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => (¬ (_raw_i5 = (M.number (0 : ℂ))))) _litex_input) (Litex.denote (Litex.number (M := M) (2 : ℂ)))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))⟩)
            have _returned_member : Litex.In _wd_1_0 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := (by
              intro _raw_i6 h_71 h_37
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_71)
              have h_71 : Litex.In _value_i6 (Litex.R (M := M)) := h_71
              have h_37 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                        exact h_37)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))) := Litex.FunctionSemantics.call_mem _returned_signature.domain _returned_signature.output (Litex.denote _value_i4) (Litex.denote (Litex.number (M := M) (2 : ℂ))) _returned_source _returned_input
            exact Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _raw_i6) → True := (by
              intro _raw_i6 h_71 h_37
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_71)
              have h_71 : Litex.In _value_i6 (Litex.R (M := M)) := h_71
              have h_37 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (¬ (_raw_i6 = (M.number (0 : ℂ))))
                        exact h_37)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) _returned_member)
            exact Litex.fnRange _wd_1_0 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ)))))) _range_signature_0))
          have h_38 : (by
            let _atomic_wd_1_0 := _object_w25
            exact Litex.IsSet _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w25
                    exact (Litex.isSet _atomic_wd_1_0))
                )
            )
          exact h_38
        )
      )
  )

theorem h_85 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_124 : Litex.In _value_i7 (let _checked_header : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → True := (by
    intro _raw_i8 h_122 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_122)
    have h_122 : Litex.In _value_i8 (Litex.R (M := M)) := h_122
    exact True.intro);
  Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → True := (by
    intro _raw_i9 h_123 _
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_123)
    have h_123 : Litex.In _value_i9 (Litex.R (M := M)) := h_123
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)))) {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_125 : Litex.In _value_i10 (Litex.R (M := M))), (by
  let _object_w37 := (let _wd_1_0 := (let _object_w35 := (Litex.add _value_i10 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_125) (Litex.numberInC (M := M) (1 : ℂ)));
  (let _litex_call_arg_0 := _object_w35;
  Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → True := (by
      intro _raw_i9 h_123 _
      let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_123)
      have h_123 : Litex.In _value_i9 (Litex.R (M := M)) := h_123
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _value_i7 _litex_call_arg_0 h_124 (by
    let _atomic_wd_1_0 := _object_w35
    exact (Litex.addInR _value_i10 (Litex.number (M := M) (1 : ℂ)) h_125 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))) True.intro));
  (by
    have _range_signature_0 : Litex.In _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))) := (by
    let _returned_signature : Litex.FunctionSignature M := (let _litex_output := (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → True := (by
      intro _raw_i9 h_123 _
      let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_123)
      have h_123 : Litex.In _value_i9 (Litex.R (M := M)) := h_123
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input))
    have _returned_source : Litex.In _value_i7 (Litex.fnSet _returned_signature) := (Litex.inOfSame _value_i7 _value_i7 (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → True := (by
      intro _raw_i9 h_123 _
      let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_123)
      have h_123 : Litex.In _value_i9 (Litex.R (M := M)) := h_123
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → True := (by
      intro _raw_i9 h_123 _
      let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_123)
      have h_123 : Litex.In _value_i9 (Litex.R (M := M)) := h_123
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (Litex.sameRefl (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → True := (by
      intro _raw_i9 h_123 _
      let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_123)
      have h_123 : Litex.In _value_i9 (Litex.R (M := M)) := h_123
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)))) h_124)
    have _returned_input : M.mem (Litex.denote (_wd_1_0).val.argument) _returned_signature.domain := (let _litex_output := (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → True := (by
      intro _raw_i9 h_123 _
      let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_123)
      have h_123 : Litex.In _value_i9 (Litex.R (M := M)) := h_123
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))); (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) (Litex.denote (_wd_1_0).val.argument)).mpr ⟨(by
    let _atomic_wd_1_0 := (_wd_1_0).val.argument
    exact (Litex.addInR _value_i10 (Litex.number (M := M) (1 : ℂ)) h_125 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))), True.intro⟩)
    have _returned_member : Litex.In _wd_1_0 (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → True := (by
      intro _raw_i9 h_123 _
      let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_123)
      have h_123 : Litex.In _value_i9 (Litex.R (M := M)) := h_123
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))) := Litex.FunctionSemantics.call_mem _returned_signature.domain _returned_signature.output (Litex.denote _value_i7) (Litex.denote (_wd_1_0).val.argument) _returned_source _returned_input
    exact Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → True := (by
      intro _raw_i9 h_123 _
      let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_123)
      have h_123 : Litex.In _value_i9 (Litex.R (M := M)) := h_123
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) _returned_member)
    exact Litex.fnRange _wd_1_0 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True)) _range_signature_0))
  exact (by
    let _atomic_wd_1_0 := _object_w37
    exact Litex.IsSet _atomic_wd_1_0)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_124 _Host_i10 _rep_i10 _value_i10 h_125
          let _object_w37 := (let _wd_1_0 := (let _object_w35 := (Litex.add _value_i10 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_125) (Litex.numberInC (M := M) (1 : ℂ)));
          (let _litex_call_arg_0 := _object_w35;
          Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → True := (by
              intro _raw_i9 h_123 _
              let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_123)
              have h_123 : Litex.In _value_i9 (Litex.R (M := M)) := h_123
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _value_i7 _litex_call_arg_0 h_124 (by
            let _atomic_wd_1_0 := _object_w35
            exact (Litex.addInR _value_i10 (Litex.number (M := M) (1 : ℂ)) h_125 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))) True.intro));
          (by
            have _range_signature_0 : Litex.In _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))) := (by
            let _returned_signature : Litex.FunctionSignature M := (let _litex_output := (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → True := (by
              intro _raw_i9 h_123 _
              let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_123)
              have h_123 : Litex.In _value_i9 (Litex.R (M := M)) := h_123
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input))
            have _returned_source : Litex.In _value_i7 (Litex.fnSet _returned_signature) := (Litex.inOfSame _value_i7 _value_i7 (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → True := (by
              intro _raw_i9 h_123 _
              let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_123)
              have h_123 : Litex.In _value_i9 (Litex.R (M := M)) := h_123
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → True := (by
              intro _raw_i9 h_123 _
              let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_123)
              have h_123 : Litex.In _value_i9 (Litex.R (M := M)) := h_123
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (Litex.sameRefl (Litex.fnSet (let _litex_output := (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → True := (by
              intro _raw_i9 h_123 _
              let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_123)
              have h_123 : Litex.In _value_i9 (Litex.R (M := M)) := h_123
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)))) h_124)
            have _returned_input : M.mem (Litex.denote (_wd_1_0).val.argument) _returned_signature.domain := (let _litex_output := (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → True := (by
              intro _raw_i9 h_123 _
              let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_123)
              have h_123 : Litex.In _value_i9 (Litex.R (M := M)) := h_123
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))); (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) (Litex.denote (_wd_1_0).val.argument)).mpr ⟨(by
            let _atomic_wd_1_0 := (_wd_1_0).val.argument
            exact (Litex.addInR _value_i10 (Litex.number (M := M) (1 : ℂ)) h_125 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))), True.intro⟩)
            have _returned_member : Litex.In _wd_1_0 (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → True := (by
              intro _raw_i9 h_123 _
              let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_123)
              have h_123 : Litex.In _value_i9 (Litex.R (M := M)) := h_123
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))) := Litex.FunctionSemantics.call_mem _returned_signature.domain _returned_signature.output (Litex.denote _value_i7) (Litex.denote (_wd_1_0).val.argument) _returned_source _returned_input
            exact Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → True := (by
              intro _raw_i9 h_123 _
              let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_123)
              have h_123 : Litex.In _value_i9 (Litex.R (M := M)) := h_123
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) _returned_member)
            exact Litex.fnRange _wd_1_0 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True)) _range_signature_0))
          have h_84 : (by
            let _atomic_wd_1_0 := _object_w37
            exact Litex.IsSet _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w37
                    exact (Litex.isSet _atomic_wd_1_0))
                )
            )
          exact h_84
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_returned_x5f_function_x5f_ranges_x2f_statement_x2e_lit
