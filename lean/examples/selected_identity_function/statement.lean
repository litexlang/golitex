import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_selected_x5f_identity_x5f_function_x2f_statement_x2e_lit

universe u v1 v9 v12
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (Litex.R (M := M))), (∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_7 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same _value_i2 _value_i1) ∧ (∀ (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.mem (Litex.denote _unique_left_i2) (M.standard Litex.StandardSetValue.real)) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.mem (Litex.denote _unique_right_i2) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i2) = (Litex.denote _value_i1))) (_body_right_0 : ((Litex.denote _unique_right_i2) = (Litex.denote _value_i1))), (Litex.denote _unique_left_i2) = (Litex.denote _unique_right_i2)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6
          have h_8 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_5 : (∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_9 : Litex.In _value_i3 (Litex.R (M := M))), Litex.Same _value_i3 _value_i1) ∧ (∀ (_unique_left_i3 : Litex.Obj (M := M) M.Value) (_member_left_i3 : M.mem (Litex.denote _unique_left_i3) (M.standard Litex.StandardSetValue.real)) (_unique_right_i3 : Litex.Obj (M := M) M.Value) (_member_right_i3 : M.mem (Litex.denote _unique_right_i3) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i3) = (Litex.denote _value_i1))) (_body_right_0 : ((Litex.denote _unique_right_i3) = (Litex.denote _value_i1))), (Litex.denote _unique_left_i3) = (Litex.denote _unique_right_i3)) :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i3 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1)
                    have h_15 : Litex.In _value_i3 (Litex.R (M := M)) := h_8
                    have h_16 : Litex.Same _value_i3 _value_i1 := rfl
                    have h_17 : Litex.Same _value_i1 _value_i1 := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ⟨⟨_value_i3, h_15, h_17⟩, (by
                      intro _unique_left_i3 _member_left_i3 _unique_right_i3 _member_right_i3 _body_left_0 _body_right_0
                      exact (show ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_47 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_48 : Litex.In _value_i6 (Litex.R (M := M))) (h_19 : Litex.Same _value_i5 _value_i1) (h_20 : Litex.Same _value_i6 _value_i1), Litex.Same _value_i5 _value_i6 from (by
                      intro _Host_i5 _rep_i5 _value_i5 h_47 _Host_i6 _rep_i6 _value_i6 h_48 h_19 h_20
                      have h_21 : Litex.Same _value_i5 _value_i6 :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((h_19).trans (h_20).symm)
                            )
                        )
                      exact h_21
                    )) _unique_left_i3 _member_left_i3 _unique_right_i3 _member_right_i3 _body_left_0 _body_right_0)⟩
                )
            )

          have h_53 : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (_membership_i7 : M.mem (Litex.denote _value_i7) (M.standard Litex.StandardSetValue.real)) {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (_membership_i8 : M.mem (Litex.denote _value_i8) (M.standard Litex.StandardSetValue.real)) (h_50 : ((Litex.denote _value_i7) = (Litex.denote _value_i1))) (h_51 : ((Litex.denote _value_i8) = (Litex.denote _value_i1))), ((Litex.denote _value_i7) = (Litex.denote _value_i8)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i7 _rep_i7 _value_i7 _membership_i7 _Host_i8 _rep_i8 _value_i8 _membership_i8 h_50 h_51
                    have _unique : ∀ (_unique_left_i3 : Litex.Obj (M := M) M.Value) (_member_left_i3 : M.mem (Litex.denote _unique_left_i3) (M.standard Litex.StandardSetValue.real)) (_unique_right_i3 : Litex.Obj (M := M) M.Value) (_member_right_i3 : M.mem (Litex.denote _unique_right_i3) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i3) = (Litex.denote _value_i1))) (_body_right_0 : ((Litex.denote _unique_right_i3) = (Litex.denote _value_i1))), (Litex.denote _unique_left_i3) = (Litex.denote _unique_right_i3) := (h_5).2
                    have _same := _unique (Litex.semanticObject (Litex.denote _value_i7) (Litex.isSet _value_i7)) _membership_i7 (Litex.semanticObject (Litex.denote _value_i8) (Litex.isSet _value_i8)) _membership_i8 h_50 h_51
                    exact _same)
                )
            )
          exact h_5
        )
      )
  )

noncomputable def _object_i11 := (show Litex.Obj (M := M) (Litex.SelectedFn M) from by
  let _selected_signature := ((show Litex.Obj (M := M) (Litex.FunctionSignature M) from (by
  have _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → True := by
    intro _raw_i9 h_64 _
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_64)
    have h_64 : Litex.In _value_i9 (Litex.R (M := M)) := h_64
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True))))).val
  have _selected_pointwise : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => True) _raw_i9) → ∃! _selected_output : M.Value, M.mem _selected_output (Litex.denote (Litex.R (M := M))) ∧ ((_selected_output = _raw_i9)) := (by
    intro _raw_i9 h_64 _
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_64)
    have h_64 : Litex.In _value_i9 (Litex.R (M := M)) := h_64
    have h_59 : ∀ {_Host_i9 : Type u} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_62 : Litex.In _value_i9 (Litex.R (M := M))), (∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_63 : Litex.In _value_i10 (Litex.R (M := M))), Litex.Same _value_i10 _value_i9) ∧ (∀ (_unique_left_i10 : Litex.Obj (M := M) M.Value) (_member_left_i10 : M.mem (Litex.denote _unique_left_i10) (M.standard Litex.StandardSetValue.real)) (_unique_right_i10 : Litex.Obj (M := M) M.Value) (_member_right_i10 : M.mem (Litex.denote _unique_right_i10) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i10) = (Litex.denote _value_i9))) (_body_right_0 : ((Litex.denote _unique_right_i10) = (Litex.denote _value_i9))), (Litex.denote _unique_left_i10) = (Litex.denote _unique_right_i10)) := (by
      intro _Host_i9 _rep_i9 _value_i9 h_62
      exact ((h_3 (M := M)) _value_i9 h_62)
    )
    obtain ⟨_selected_exists, _selected_unique⟩ := h_59 _value_i9 h_64
    apply Litex.existsUniqueValueOfObjects (Litex.denote (Litex.R (M := M))) (fun _selected_output => (_selected_output = _raw_i9))
    · obtain ⟨_selected_witness, _selected_member, _selected_clause_0⟩ := _selected_exists
      exact ⟨_selected_witness, _selected_member, _selected_clause_0⟩
    · intro _selected_left _selected_right _selected_left_member _selected_right_member _selected_left_body _selected_right_body
      exact _selected_unique _selected_left _selected_left_member _selected_right _selected_right_member _selected_left_body _selected_right_body)
  exact Litex.selectedFn _selected_signature (fun (_selected_input _selected_output : M.Value) => (_selected_output = _selected_input)) (by
    intro _selected_input _selected_domain
    obtain ⟨_selected_members, _selected_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _selected_input).mp _selected_domain
    exact _selected_pointwise _selected_input _selected_members _selected_guard))

theorem h_65 : Litex.In (_object_i11 (M := M)) (Litex.fnSet ((_object_i11 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.selectedFnInFnSet (_object_i11 (M := M)))
      )
  )

theorem h_67 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_68 : M.mem (Litex.denote _value_i9) (M.standard Litex.StandardSetValue.real)), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.denote _value_i9)) = (Litex.denote _value_i9)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i9 _rep_i9 _value_i9 h_68
          have _selected_domain : M.mem (Litex.denote _value_i9) ((_object_i11 (M := M))).val.signature.domain := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) (Litex.denote _value_i9)).mpr ⟨h_68, (Eq.mpr rfl (True.intro : (fun (_raw_i9 : M.Value) => True) (Litex.denote _value_i9)))⟩
          exact Eq.mp rfl (Litex.selectedFn_call_spec (_object_i11 (M := M)) (Litex.denote _value_i9) _selected_domain).2)
      )
  )

theorem h_76 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_68 : M.mem (Litex.denote _value_i9) (M.standard Litex.StandardSetValue.real)) {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (_membership_i12 : M.mem (Litex.denote _value_i12) (M.standard Litex.StandardSetValue.real)) (h_74 : ((Litex.denote _value_i12) = (Litex.denote _value_i9))), ((Litex.denote _value_i12) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.denote _value_i9))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i9 _rep_i9 _value_i9 h_68 _Host_i12 _rep_i12 _value_i12 _membership_i12 h_74
          have _selected_domain : M.mem (Litex.denote _value_i9) ((_object_i11 (M := M))).val.signature.domain := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) (Litex.denote _value_i9)).mpr ⟨h_68, (Eq.mpr rfl (True.intro : (fun (_raw_i9 : M.Value) => True) (Litex.denote _value_i9)))⟩
          apply Litex.selectedFn_unique (_object_i11 (M := M)) (Litex.denote _value_i9) (Litex.denote _value_i12) _selected_domain
          refine ⟨_membership_i12, ?_⟩
          exact Eq.mpr rfl (h_74 : ((Litex.denote _value_i12) = (Litex.denote _value_i9))))
      )
  )

noncomputable def _object_w8 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => True) (_object_i11 (M := M)) (Litex.number (M := M) (3 : ℂ)) (h_65 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro)

theorem h_77 : (by
  let _equal_wd_1_0 := (_object_w8 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_99 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) :=
            (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))
          exact (Eq.trans (Eq.symm (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i11 (M := M))) (Litex.sameRefl (Litex.number (M := M) (3 : ℂ))))) (Eq.trans ((h_67 (M := M)) (Litex.number (M := M) (3 : ℂ)) h_99) (Litex.sameRefl (Litex.number (M := M) (3 : ℂ)))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_selected_x5f_identity_x5f_function_x2f_statement_x2e_lit
