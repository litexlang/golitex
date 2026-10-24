import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_bijective_x5f_unique_x5f_preimages_x2f_statement_x2e_lit

universe u v1 v2 v3 v5 v11 v12 v13 v15
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_7 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_8 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_10 : Litex.In _value_i3 (by
  have _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _value_i1) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := by
    intro _raw_i4 h_9 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_9)
    have h_9 : Litex.In _value_i4 _value_i1 := h_9
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.isSet _value_i1) (Litex.isSet _value_i2) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_11 : Litex.In _value_i5 _value_i2) (h_1 : (Litex.bijectiveValue (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.denote _value_i3))), (∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_32 : Litex.In _value_i6 _value_i1), Litex.Same (let _litex_call_arg_0 := _value_i6;
Litex.callOnDomain _value_i1 _value_i2 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_10 h_32 True.intro) _value_i5) ∧ (∀ (_unique_left_i6 : Litex.Obj (M := M) M.Value) (_member_left_i6 : M.mem (Litex.denote _unique_left_i6) (Litex.denote _value_i1)) (_unique_right_i6 : Litex.Obj (M := M) M.Value) (_member_right_i6 : M.mem (Litex.denote _unique_right_i6) (Litex.denote _value_i1)) (_body_left_0 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.denote _unique_left_i6)) = (Litex.denote _value_i5))) (_body_right_0 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.denote _unique_right_i6)) = (Litex.denote _value_i5))), (Litex.denote _unique_left_i6) = (Litex.denote _unique_right_i6)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_7 _Host_i2 _rep_i2 _value_i2 h_8 _Host_i3 _rep_i3 _value_i3 h_10 _Host_i5 _rep_i5 _value_i5 h_11 h_1
          have h_30 : (Litex.injectiveValue (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.denote _value_i3)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_1).1
                )
            )
          have h_31 : (Litex.surjectiveValue (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.denote _value_i3)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_1).2
                )
            )
          have h_3 : (∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_32 : Litex.In _value_i6 _value_i1), Litex.Same (let _litex_call_arg_0 := _value_i6;
          Litex.callOnDomain _value_i1 _value_i2 (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_10 h_32 True.intro) _value_i5) ∧ (∀ (_unique_left_i6 : Litex.Obj (M := M) M.Value) (_member_left_i6 : M.mem (Litex.denote _unique_left_i6) (Litex.denote _value_i1)) (_unique_right_i6 : Litex.Obj (M := M) M.Value) (_member_right_i6 : M.mem (Litex.denote _unique_right_i6) (Litex.denote _value_i1)) (_body_left_0 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.denote _unique_left_i6)) = (Litex.denote _value_i5))) (_body_right_0 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.denote _unique_right_i6)) = (Litex.denote _value_i5))), (Litex.denote _unique_left_i6) = (Litex.denote _unique_right_i6)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.bijectiveValue_preimage (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.denote _value_i3) (Litex.denote _value_i5) h_1 h_11)
                )
            )
          have h_51 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (_membership_i9 : M.mem (Litex.denote _value_i9) (Litex.denote _value_i1)) {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (_membership_i10 : M.mem (Litex.denote _value_i10) (Litex.denote _value_i1)) (h_48 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.denote _value_i9)) = (Litex.denote _value_i5))) (h_49 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.denote _value_i10)) = (Litex.denote _value_i5))), ((Litex.denote _value_i9) = (Litex.denote _value_i10)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i9 _rep_i9 _value_i9 _membership_i9 _Host_i10 _rep_i10 _value_i10 _membership_i10 h_48 h_49
                    have _unique : ∀ (_unique_left_i6 : Litex.Obj (M := M) M.Value) (_member_left_i6 : M.mem (Litex.denote _unique_left_i6) (Litex.denote _value_i1)) (_unique_right_i6 : Litex.Obj (M := M) M.Value) (_member_right_i6 : M.mem (Litex.denote _unique_right_i6) (Litex.denote _value_i1)) (_body_left_0 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.denote _unique_left_i6)) = (Litex.denote _value_i5))) (_body_right_0 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (Litex.denote _unique_right_i6)) = (Litex.denote _value_i5))), (Litex.denote _unique_left_i6) = (Litex.denote _unique_right_i6) := (h_3).2
                    have _same := _unique (Litex.semanticObject (Litex.denote _value_i9) (Litex.isSet _value_i9)) _membership_i9 (Litex.semanticObject (Litex.denote _value_i10) (Litex.isSet _value_i10)) _membership_i10 h_48 h_49
                    exact _same)
                )
            )
          exact h_3
        )
      )
  )

theorem h_55 : ∀ {_Host_i11 : Type v11} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_61 : Litex.IsSet _value_i11) {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_62 : Litex.IsSet _value_i12) {_Host_i13 : Type v13} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_64 : Litex.In _value_i13 (by
  have _checked_header : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (Litex.denote _value_i11) → ((fun (_raw_i14 : M.Value) => True) _raw_i14) → True := by
    intro _raw_i14 h_63 _
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_63)
    have h_63 : Litex.In _value_i14 _value_i11 := h_63
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i11) (Litex.denote _value_i12) (Litex.isSet _value_i11) (Litex.isSet _value_i12) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) => True) _litex_input)))) {_Host_i15 : Type v15} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_65 : Litex.In _value_i15 _value_i12) (h_52 : (Litex.bijectiveValue (Litex.denote _value_i11) (Litex.denote _value_i12) (Litex.denote _value_i13))), (∃ (_value_i16 : Litex.Obj (M := M) M.Value), ∃ (h_86 : Litex.In _value_i16 _value_i11), Litex.Same _value_i15 (let _litex_call_arg_0 := _value_i16;
Litex.callOnDomain _value_i11 _value_i12 (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) => True) _litex_input) _value_i13 _litex_call_arg_0 h_64 h_86 True.intro)) ∧ (∀ (_unique_left_i16 : Litex.Obj (M := M) M.Value) (_member_left_i16 : M.mem (Litex.denote _unique_left_i16) (Litex.denote _value_i11)) (_unique_right_i16 : Litex.Obj (M := M) M.Value) (_member_right_i16 : M.mem (Litex.denote _unique_right_i16) (Litex.denote _value_i11)) (_body_left_0 : ((Litex.denote _value_i15) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i13) (Litex.denote _unique_left_i16)))) (_body_right_0 : ((Litex.denote _value_i15) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i13) (Litex.denote _unique_right_i16)))), (Litex.denote _unique_left_i16) = (Litex.denote _unique_right_i16)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i11 _rep_i11 _value_i11 h_61 _Host_i12 _rep_i12 _value_i12 h_62 _Host_i13 _rep_i13 _value_i13 h_64 _Host_i15 _rep_i15 _value_i15 h_65 h_52
          have h_84 : (Litex.injectiveValue (Litex.denote _value_i11) (Litex.denote _value_i12) (Litex.denote _value_i13)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_52).1
                )
            )
          have h_85 : (Litex.surjectiveValue (Litex.denote _value_i11) (Litex.denote _value_i12) (Litex.denote _value_i13)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_52).2
                )
            )
          have h_54 : (∃ (_value_i16 : Litex.Obj (M := M) M.Value), ∃ (h_86 : Litex.In _value_i16 _value_i11), Litex.Same _value_i15 (let _litex_call_arg_0 := _value_i16;
          Litex.callOnDomain _value_i11 _value_i12 (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) => True) _litex_input) _value_i13 _litex_call_arg_0 h_64 h_86 True.intro)) ∧ (∀ (_unique_left_i16 : Litex.Obj (M := M) M.Value) (_member_left_i16 : M.mem (Litex.denote _unique_left_i16) (Litex.denote _value_i11)) (_unique_right_i16 : Litex.Obj (M := M) M.Value) (_member_right_i16 : M.mem (Litex.denote _unique_right_i16) (Litex.denote _value_i11)) (_body_left_0 : ((Litex.denote _value_i15) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i13) (Litex.denote _unique_left_i16)))) (_body_right_0 : ((Litex.denote _value_i15) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i13) (Litex.denote _unique_right_i16)))), (Litex.denote _unique_left_i16) = (Litex.denote _unique_right_i16)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _preimage := (Litex.bijectiveValue_preimage (Litex.denote _value_i11) (Litex.denote _value_i12) (Litex.denote _value_i13) (Litex.denote _value_i15) h_52 h_65)
                    constructor
                    · obtain ⟨_x, _hx, _eq⟩ := _preimage.1
                      exact ⟨_x, _hx, _eq.symm⟩
                    · intro _x _hx _z _hz _ex _ez
                      exact _preimage.2 _x _hx _z _hz _ex.symm _ez.symm)
                )
            )
          have h_105 : ∀ {_Host_i19 : Type _} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (_membership_i19 : M.mem (Litex.denote _value_i19) (Litex.denote _value_i11)) {_Host_i20 : Type _} [_rep_i20 : Litex.Representation M _Host_i20] (_value_i20 : Litex.Obj (M := M) _Host_i20) (_membership_i20 : M.mem (Litex.denote _value_i20) (Litex.denote _value_i11)) (h_102 : ((Litex.denote _value_i15) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i13) (Litex.denote _value_i19)))) (h_103 : ((Litex.denote _value_i15) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i13) (Litex.denote _value_i20)))), ((Litex.denote _value_i19) = (Litex.denote _value_i20)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i19 _rep_i19 _value_i19 _membership_i19 _Host_i20 _rep_i20 _value_i20 _membership_i20 h_102 h_103
                    have _unique : ∀ (_unique_left_i16 : Litex.Obj (M := M) M.Value) (_member_left_i16 : M.mem (Litex.denote _unique_left_i16) (Litex.denote _value_i11)) (_unique_right_i16 : Litex.Obj (M := M) M.Value) (_member_right_i16 : M.mem (Litex.denote _unique_right_i16) (Litex.denote _value_i11)) (_body_left_0 : ((Litex.denote _value_i15) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i13) (Litex.denote _unique_left_i16)))) (_body_right_0 : ((Litex.denote _value_i15) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i13) (Litex.denote _unique_right_i16)))), (Litex.denote _unique_left_i16) = (Litex.denote _unique_right_i16) := (h_54).2
                    have _same := _unique (Litex.semanticObject (Litex.denote _value_i19) (Litex.isSet _value_i19)) _membership_i19 (Litex.semanticObject (Litex.denote _value_i20) (Litex.isSet _value_i20)) _membership_i20 h_102 h_103
                    exact _same)
                )
            )
          exact h_54
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_bijective_x5f_unique_x5f_preimages_x2f_statement_x2e_lit
