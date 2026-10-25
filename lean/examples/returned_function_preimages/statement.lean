import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_returned_x5f_function_x5f_preimages_x2f_statement_x2e_lit

universe u v1
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
  let _object_w12 := (let _wd_1_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
  Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_28 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
      have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_29 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro);
  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
  (by
    let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_37 : Litex.In _value_i4 (Litex.R (M := M))) => Litex.Same (by
    let _returned_receiver := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
  Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_28 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
      have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_29 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro)
    let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))
    have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
    have _returned_domain : M.mem (Litex.denote _value_i4) _returned_signature.domain := ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (Litex.denote _value_i4)).mpr ⟨h_37, True.intro⟩)
    exact Litex.callOn _returned_signature _returned_receiver _value_i4 _returned_member _returned_domain) _wd_1_1))
    exact Litex.preimage _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)) (by
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
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) _returned_member)))
  exact (by
    let _atomic_wd_1_0 := _object_w12
    exact Litex.IsSet _atomic_wd_1_0)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_29
          let _object_w12 := (let _wd_1_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
          Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_28 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
              have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_29 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro);
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (by
            let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_37 : Litex.In _value_i4 (Litex.R (M := M))) => Litex.Same (by
            let _returned_receiver := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
          Litex.callOnDomain (Litex.R (M := M)) (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_28 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
              have h_28 : Litex.In _value_i3 (Litex.R (M := M)) := h_28
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_29 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) True.intro)
            let _returned_signature : Litex.FunctionSignature M := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))
            have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver
            have _returned_domain : M.mem (Litex.denote _value_i4) _returned_signature.domain := ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) (Litex.denote _value_i4)).mpr ⟨h_37, True.intro⟩)
            exact Litex.callOn _returned_signature _returned_receiver _value_i4 _returned_member _returned_domain) _wd_1_1))
            exact Litex.preimage _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)) (by
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
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) _returned_member)))
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w12
            exact Litex.IsSet _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w12
                    exact (Litex.isSet _atomic_wd_1_0))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_returned_x5f_function_x5f_preimages_x2f_statement_x2e_lit
