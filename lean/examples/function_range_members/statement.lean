import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_range_x5f_members_x2f_statement_x2e_lit

universe u v1 v2 v3 v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_7 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_8 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_10 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_9 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_9)
    have h_9 : Litex.In _value_i4 _value_i1 := h_9
    exact True.intro);
  Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_11 : Litex.In _value_i5 (by
  have _range_signature_0 : Litex.In _value_i3 (Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) := (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_9 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_9)
    have h_9 : Litex.In _value_i4 _value_i1 := h_9
    exact True.intro);
  Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_10)
  exact Litex.fnRange _value_i3 (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) _range_signature_0)), ((Litex.In _value_i5 _value_i2) ∧ (∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_25 : Litex.In _value_i6 _value_i1), Litex.Same _value_i5 (let _litex_call_arg_0 := _value_i6;
Litex.callOnDomain _value_i1 _value_i2 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_10 h_25 True.intro))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_7 _Host_i2 _rep_i2 _value_i2 h_8 _Host_i3 _rep_i3 _value_i3 h_10 _Host_i5 _rep_i5 _value_i5 h_11
          have h_12 : Litex.In _value_i5 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.fnRangeInOutput (by
                    have _range_signature_0 : Litex.In _value_i3 (Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) := (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                      intro _raw_i4 h_9 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_9)
                      have h_9 : Litex.In _value_i4 _value_i1 := h_9
                      exact True.intro);
                    Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_10)
                    exact Litex.fnRange _value_i3 (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) _range_signature_0) _value_i5 (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (Litex.inOfSame _value_i3 _value_i3 (Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) (Litex.sameRefl _value_i3) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))) h_10) h_11)
                )
            )
          have h_14 : ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (_member_i7 : M.mem (Litex.denote _value_i7) (Litex.denote _value_i1)), ((Litex.denote _value_i5) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.denote _value_i7))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    obtain ⟨_range_input, _range_domain, _range_eq⟩ := (Litex.inFnRange_iff (by
                    have _range_signature_0 : Litex.In _value_i3 (Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) := (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                      intro _raw_i4 h_9 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_9)
                      have h_9 : Litex.In _value_i4 _value_i1 := h_9
                      exact True.intro);
                    Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_10)
                    exact Litex.fnRange _value_i3 (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) _range_signature_0) _value_i5 (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (Litex.inOfSame _value_i3 _value_i3 (Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input))) (Litex.sameRefl _value_i3) (Litex.sameRefl (Litex.fnSet (let _litex_output := _value_i2; Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _litex_output) (Litex.isSet _value_i1) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))) h_10)).mp h_11
                    obtain ⟨_range_members, _range_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.isSet _value_i1) (Litex.isSet _value_i2) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _).mp _range_domain
                    have _range_base_member_0 := _range_members
                    have _range_member_0 := _range_base_member_0
                    exact ⟨(Litex.semanticObject (Litex.denote _range_input) (M.member_isSet _range_member_0)), _range_member_0, _range_eq⟩)
                )
            )
          have h_1 : Litex.In _value_i5 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  h_12
                )
            )
          have h_3 : ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_25 : Litex.In _value_i6 _value_i1), Litex.Same _value_i5 (let _litex_call_arg_0 := _value_i6;
          Litex.callOnDomain _value_i1 _value_i2 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_10 h_25 True.intro) :=
            (by
              litex_checked_step =>
                exact (
                  h_14
                )
            )
          exact (And.intro h_1 h_3)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_range_x5f_members_x2f_statement_x2e_lit
