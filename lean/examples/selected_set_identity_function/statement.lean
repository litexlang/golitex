import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_selected_x5f_set_x5f_identity_x5f_function_x2f_statement_x2e_lit

universe u v1 v2 v10 v13 v14
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

variable {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1)

theorem h_4 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_7 : Litex.In _value_i2 _value_i1), (∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_8 : Litex.In _value_i3 _value_i1), Litex.Same _value_i3 _value_i2) ∧ (∀ (_unique_left_i3 : Litex.Obj (M := M) M.Value) (_member_left_i3 : M.mem (Litex.denote _unique_left_i3) (Litex.denote _value_i1)) (_unique_right_i3 : Litex.Obj (M := M) M.Value) (_member_right_i3 : M.mem (Litex.denote _unique_right_i3) (Litex.denote _value_i1)) (_body_left_0 : ((Litex.denote _unique_left_i3) = (Litex.denote _value_i2))) (_body_right_0 : ((Litex.denote _unique_right_i3) = (Litex.denote _value_i2))), (Litex.denote _unique_left_i3) = (Litex.denote _unique_right_i3)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_7
          have h_9 : Litex.In _value_i2 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          have h_6 : (∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_10 : Litex.In _value_i4 _value_i1), Litex.Same _value_i4 _value_i2) ∧ (∀ (_unique_left_i4 : Litex.Obj (M := M) M.Value) (_member_left_i4 : M.mem (Litex.denote _unique_left_i4) (Litex.denote _value_i1)) (_unique_right_i4 : Litex.Obj (M := M) M.Value) (_member_right_i4 : M.mem (Litex.denote _unique_right_i4) (Litex.denote _value_i1)) (_body_left_0 : ((Litex.denote _unique_left_i4) = (Litex.denote _value_i2))) (_body_right_0 : ((Litex.denote _unique_right_i4) = (Litex.denote _value_i2))), (Litex.denote _unique_left_i4) = (Litex.denote _unique_right_i4)) :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i4 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote _value_i2) (Litex.isSet _value_i2)
                    have h_16 : Litex.In _value_i4 _value_i1 := h_9
                    have h_17 : Litex.Same _value_i4 _value_i2 := rfl
                    have h_18 : Litex.Same _value_i2 _value_i2 := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ⟨⟨_value_i4, h_16, h_18⟩, (by
                      intro _unique_left_i4 _member_left_i4 _unique_right_i4 _member_right_i4 _body_left_0 _body_right_0
                      exact (show ∀ {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_48 : Litex.In _value_i6 _value_i1) {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_49 : Litex.In _value_i7 _value_i1) (h_20 : Litex.Same _value_i6 _value_i2) (h_21 : Litex.Same _value_i7 _value_i2), Litex.Same _value_i6 _value_i7 from (by
                      intro _Host_i6 _rep_i6 _value_i6 h_48 _Host_i7 _rep_i7 _value_i7 h_49 h_20 h_21
                      have h_22 : Litex.Same _value_i6 _value_i7 :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((h_20).trans (h_21).symm)
                            )
                        )
                      exact h_22
                    )) _unique_left_i4 _member_left_i4 _unique_right_i4 _member_right_i4 _body_left_0 _body_right_0)⟩
                )
            )

          have h_54 : ∀ {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (_membership_i8 : M.mem (Litex.denote _value_i8) (Litex.denote _value_i1)) {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (_membership_i9 : M.mem (Litex.denote _value_i9) (Litex.denote _value_i1)) (h_51 : ((Litex.denote _value_i8) = (Litex.denote _value_i2))) (h_52 : ((Litex.denote _value_i9) = (Litex.denote _value_i2))), ((Litex.denote _value_i8) = (Litex.denote _value_i9)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i8 _rep_i8 _value_i8 _membership_i8 _Host_i9 _rep_i9 _value_i9 _membership_i9 h_51 h_52
                    have _unique : ∀ (_unique_left_i4 : Litex.Obj (M := M) M.Value) (_member_left_i4 : M.mem (Litex.denote _unique_left_i4) (Litex.denote _value_i1)) (_unique_right_i4 : Litex.Obj (M := M) M.Value) (_member_right_i4 : M.mem (Litex.denote _unique_right_i4) (Litex.denote _value_i1)) (_body_left_0 : ((Litex.denote _unique_left_i4) = (Litex.denote _value_i2))) (_body_right_0 : ((Litex.denote _unique_right_i4) = (Litex.denote _value_i2))), (Litex.denote _unique_left_i4) = (Litex.denote _unique_right_i4) := (h_6).2
                    have _same := _unique (Litex.semanticObject (Litex.denote _value_i8) (Litex.isSet _value_i8)) _membership_i8 (Litex.semanticObject (Litex.denote _value_i9) (Litex.isSet _value_i9)) _membership_i9 h_51 h_52
                    exact _same)
                )
            )
          exact h_6
        )
      )
  )

noncomputable def _object_i12 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) := (show Litex.Obj (M := M) (Litex.SelectedFn M) from by
  let _selected_signature := ((show Litex.Obj (M := M) (Litex.FunctionSignature M) from (by
  have _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote _value_i1) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → True := by
    intro _raw_i10 h_65 _
    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_65)
    have h_65 : Litex.In _value_i10 _value_i1 := h_65
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.withGuard (M := M) (Litex.denote _value_i1) (Litex.denote _value_i1) (Litex.isSet _value_i1) (Litex.isSet _value_i1) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input))))).val
  have _selected_pointwise : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote _value_i1) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → ∃! _selected_output : M.Value, M.mem _selected_output (Litex.denote _value_i1) ∧ ((_selected_output = _raw_i10)) := (by
    intro _raw_i10 h_65 _
    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_65)
    have h_65 : Litex.In _value_i10 _value_i1 := h_65
    have h_60 : ∀ {_Host_i10 : Type u} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_63 : Litex.In _value_i10 _value_i1), (∃ (_value_i11 : Litex.Obj (M := M) M.Value), ∃ (h_64 : Litex.In _value_i11 _value_i1), Litex.Same _value_i11 _value_i10) ∧ (∀ (_unique_left_i11 : Litex.Obj (M := M) M.Value) (_member_left_i11 : M.mem (Litex.denote _unique_left_i11) (Litex.denote _value_i1)) (_unique_right_i11 : Litex.Obj (M := M) M.Value) (_member_right_i11 : M.mem (Litex.denote _unique_right_i11) (Litex.denote _value_i1)) (_body_left_0 : ((Litex.denote _unique_left_i11) = (Litex.denote _value_i10))) (_body_right_0 : ((Litex.denote _unique_right_i11) = (Litex.denote _value_i10))), (Litex.denote _unique_left_i11) = (Litex.denote _unique_right_i11)) := (by
      intro _Host_i10 _rep_i10 _value_i10 h_63
      exact ((h_4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1) _value_i10 h_63)
    )
    obtain ⟨_selected_exists, _selected_unique⟩ := h_60 _value_i10 h_65
    apply Litex.existsUniqueValueOfObjects (Litex.denote _value_i1) (fun _selected_output => (_selected_output = _raw_i10))
    · obtain ⟨_selected_witness, _selected_member, _selected_clause_0⟩ := _selected_exists
      exact ⟨_selected_witness, _selected_member, _selected_clause_0⟩
    · intro _selected_left _selected_right _selected_left_member _selected_right_member _selected_left_body _selected_right_body
      exact _selected_unique _selected_left _selected_left_member _selected_right _selected_right_member _selected_left_body _selected_right_body)
  exact Litex.selectedFn _selected_signature (fun (_selected_input _selected_output : M.Value) => (_selected_output = _selected_input)) (by
    intro _selected_input _selected_domain
    obtain ⟨_selected_members, _selected_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _value_i1) (Litex.denote _value_i1) (Litex.isSet _value_i1) (Litex.isSet _value_i1) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) _selected_input).mp _selected_domain
    exact _selected_pointwise _selected_input _selected_members _selected_guard))

theorem h_66 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : Litex.In (_object_i12 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1) (Litex.fnSet ((_object_i12 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1)).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.selectedFnInFnSet (_object_i12 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1))
      )
  )

theorem h_68 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_69 : M.mem (Litex.denote _value_i10) (Litex.denote _value_i1)), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i12 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1)) (Litex.denote _value_i10)) = (Litex.denote _value_i10)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i10 _rep_i10 _value_i10 h_69
          have _selected_domain : M.mem (Litex.denote _value_i10) ((_object_i12 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1)).val.signature.domain := (Litex.FunctionSignature.withGuard_domain (Litex.denote _value_i1) (Litex.denote _value_i1) (Litex.isSet _value_i1) (Litex.isSet _value_i1) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) (Litex.denote _value_i10)).mpr ⟨h_69, (Eq.mpr rfl (True.intro : (fun (_raw_i10 : M.Value) => True) (Litex.denote _value_i10)))⟩
          exact Eq.mp rfl (Litex.selectedFn_call_spec (_object_i12 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1) (Litex.denote _value_i10) _selected_domain).2)
      )
  )

theorem h_77 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_69 : M.mem (Litex.denote _value_i10) (Litex.denote _value_i1)) {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (_membership_i13 : M.mem (Litex.denote _value_i13) (Litex.denote _value_i1)) (h_75 : ((Litex.denote _value_i13) = (Litex.denote _value_i10))), ((Litex.denote _value_i13) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i12 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1)) (Litex.denote _value_i10))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i10 _rep_i10 _value_i10 h_69 _Host_i13 _rep_i13 _value_i13 _membership_i13 h_75
          have _selected_domain : M.mem (Litex.denote _value_i10) ((_object_i12 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1)).val.signature.domain := (Litex.FunctionSignature.withGuard_domain (Litex.denote _value_i1) (Litex.denote _value_i1) (Litex.isSet _value_i1) (Litex.isSet _value_i1) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) (Litex.denote _value_i10)).mpr ⟨h_69, (Eq.mpr rfl (True.intro : (fun (_raw_i10 : M.Value) => True) (Litex.denote _value_i10)))⟩
          apply Litex.selectedFn_unique (_object_i12 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1) (Litex.denote _value_i10) (Litex.denote _value_i13) _selected_domain
          refine ⟨_membership_i13, ?_⟩
          exact Eq.mpr rfl (h_75 : ((Litex.denote _value_i13) = (Litex.denote _value_i10))))
      )
  )

theorem h_79 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : ∀ {_Host_i14 : Type v14} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_81 : Litex.In _value_i14 _value_i1), Litex.Same (let _litex_call_arg_0 := _value_i14;
Litex.callOnDomain _value_i1 _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input) (_object_i12 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1) _litex_call_arg_0 (h_66 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1) h_81 True.intro) _value_i14 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i14 _rep_i14 _value_i14 h_81
          exact ((h_68 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1) _value_i14 h_81)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_selected_x5f_set_x5f_identity_x5f_function_x2f_statement_x2e_lit
