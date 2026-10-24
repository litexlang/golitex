import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_selected_x5f_reciprocal_x5f_function_x2f_statement_x2e_lit

universe u v1 v9 v12
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_7 : Litex.In _value_i1 (Litex.R (M := M))) (h_1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))), (∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_8 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same _value_i2 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_7) h_1)) ∧ (∀ (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.mem (Litex.denote _unique_left_i2) (M.standard Litex.StandardSetValue.real)) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.mem (Litex.denote _unique_right_i2) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i2) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))) (_body_right_0 : ((Litex.denote _unique_right_i2) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))), (Litex.denote _unique_left_i2) = (Litex.denote _unique_right_i2)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_7 h_1
          have h_33 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          have h_6 : (∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_34 : Litex.In _value_i3 (Litex.R (M := M))), Litex.Same _value_i3 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_33) h_1)) ∧ (∀ (_unique_left_i3 : Litex.Obj (M := M) M.Value) (_member_left_i3 : M.mem (Litex.denote _unique_left_i3) (M.standard Litex.StandardSetValue.real)) (_unique_right_i3 : Litex.Obj (M := M) M.Value) (_member_right_i3 : M.mem (Litex.denote _unique_right_i3) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i3) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))) (_body_right_0 : ((Litex.denote _unique_right_i3) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))), (Litex.denote _unique_left_i3) = (Litex.denote _unique_right_i3)) :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i3 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_33) h_1)) (Litex.isSet (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_33) h_1))
                    have h_106 : Litex.In _value_i3 (Litex.R (M := M)) := (by
                      let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_33) h_1)
                      exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) h_33 (_atomic_wd_1_0).wd.2.2))
                    have h_107 : Litex.Same _value_i3 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_33) h_1) := rfl
                    have h_108 : (by
                      let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_33) h_1)
                      let _equal_wd_1_1 := _equal_wd_1_0
                      exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ⟨⟨_value_i3, h_106, h_108⟩, (by
                      intro _unique_left_i3 _member_left_i3 _unique_right_i3 _member_right_i3 _body_left_0 _body_right_0
                      exact (show ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_138 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_139 : Litex.In _value_i6 (Litex.R (M := M))) (h_110 : (by
                      let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_33) h_1)
                      exact Litex.Same _value_i5 _equal_wd_1_1)) (h_111 : (by
                      let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_33) h_1)
                      exact Litex.Same _value_i6 _equal_wd_1_1)), Litex.Same _value_i5 _value_i6 from (by
                      intro _Host_i5 _rep_i5 _value_i5 h_138 _Host_i6 _rep_i6 _value_i6 h_139 h_110 h_111
                      have h_112 : Litex.Same _value_i5 _value_i6 :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((h_110).trans (h_111).symm)
                            )
                        )
                      exact h_112
                    )) _unique_left_i3 _member_left_i3 _unique_right_i3 _member_right_i3 _body_left_0 _body_right_0)⟩
                )
            )

          have h_144 : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (_membership_i7 : M.mem (Litex.denote _value_i7) (M.standard Litex.StandardSetValue.real)) {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (_membership_i8 : M.mem (Litex.denote _value_i8) (M.standard Litex.StandardSetValue.real)) (h_141 : ((Litex.denote _value_i7) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))) (h_142 : ((Litex.denote _value_i8) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))), ((Litex.denote _value_i7) = (Litex.denote _value_i8)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i7 _rep_i7 _value_i7 _membership_i7 _Host_i8 _rep_i8 _value_i8 _membership_i8 h_141 h_142
                    have _unique : ∀ (_unique_left_i3 : Litex.Obj (M := M) M.Value) (_member_left_i3 : M.mem (Litex.denote _unique_left_i3) (M.standard Litex.StandardSetValue.real)) (_unique_right_i3 : Litex.Obj (M := M) M.Value) (_member_right_i3 : M.mem (Litex.denote _unique_right_i3) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i3) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))) (_body_right_0 : ((Litex.denote _unique_right_i3) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))), (Litex.denote _unique_left_i3) = (Litex.denote _unique_right_i3) := (h_6).2
                    have _same := _unique (Litex.semanticObject (Litex.denote _value_i7) (Litex.isSet _value_i7)) _membership_i7 (Litex.semanticObject (Litex.denote _value_i8) (Litex.isSet _value_i8)) _membership_i8 h_141 h_142
                    exact _same)
                )
            )
          exact h_6
        )
      )
  )

noncomputable def _object_i11 := (show Litex.Obj (M := M) (Litex.SelectedFn M) from by
  let _selected_signature := ((show Litex.Obj (M := M) (Litex.FunctionSignature M) from (by
  have _checked_header : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) _raw_i9) → True := by
    intro _raw_i9 h_229 h_196
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_229)
    have h_229 : Litex.In _value_i9 (Litex.R (M := M)) := h_229
    have h_196 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i9 = (M.number (0 : ℂ))))
              exact h_196)
          )
      )
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))))))).val
  have _selected_pointwise : ∀ (_raw_i9 : M.Value), M.mem _raw_i9 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) _raw_i9) → ∃! _selected_output : M.Value, M.mem _selected_output (Litex.denote (Litex.R (M := M))) ∧ ((_selected_output = (M.divValue (M.number (1 : ℂ)) _raw_i9))) := (by
    intro _raw_i9 h_229 h_196
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_229)
    have h_229 : Litex.In _value_i9 (Litex.R (M := M)) := h_229
    have h_196 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i9 = (M.number (0 : ℂ))))
              exact h_196)
          )
      )
    have h_199 : ∀ {_Host_i9 : Type u} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_203 : Litex.In _value_i9 (Litex.R (M := M))) (h_196 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ))), (∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_204 : Litex.In _value_i10 (Litex.R (M := M))), Litex.Same _value_i10 (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_203) h_196)) ∧ (∀ (_unique_left_i10 : Litex.Obj (M := M) M.Value) (_member_left_i10 : M.mem (Litex.denote _unique_left_i10) (M.standard Litex.StandardSetValue.real)) (_unique_right_i10 : Litex.Obj (M := M) M.Value) (_member_right_i10 : M.mem (Litex.denote _unique_right_i10) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i10) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)))) (_body_right_0 : ((Litex.denote _unique_right_i10) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)))), (Litex.denote _unique_left_i10) = (Litex.denote _unique_right_i10)) := (by
      intro _Host_i9 _rep_i9 _value_i9 h_203 h_196
      exact ((h_4 (M := M)) _value_i9 h_203 h_196)
    )
    obtain ⟨_selected_exists, _selected_unique⟩ := h_199 _value_i9 h_229 h_196
    apply Litex.existsUniqueValueOfObjects (Litex.denote (Litex.R (M := M))) (fun _selected_output => (_selected_output = (M.divValue (M.number (1 : ℂ)) _raw_i9)))
    · obtain ⟨_selected_witness, _selected_member, _selected_clause_0⟩ := _selected_exists
      exact ⟨_selected_witness, _selected_member, _selected_clause_0⟩
    · intro _selected_left _selected_right _selected_left_member _selected_right_member _selected_left_body _selected_right_body
      exact _selected_unique _selected_left _selected_left_member _selected_right _selected_right_member _selected_left_body _selected_right_body)
  exact Litex.selectedFn _selected_signature (fun (_selected_input _selected_output : M.Value) => (_selected_output = (M.divValue (M.number (1 : ℂ)) _selected_input))) (by
    intro _selected_input _selected_domain
    obtain ⟨_selected_members, _selected_guard⟩ := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) _litex_input) _selected_input).mp _selected_domain
    exact _selected_pointwise _selected_input _selected_members _selected_guard))

theorem h_230 : Litex.In (_object_i11 (M := M)) (Litex.fnSet ((_object_i11 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.selectedFnInFnSet (_object_i11 (M := M)))
      )
  )

theorem h_232 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_233 : M.mem (Litex.denote _value_i9) (M.standard Litex.StandardSetValue.real)) (h_196 : (¬ ((Litex.denote _value_i9) = (M.number (0 : ℂ))))), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.denote _value_i9)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i9 _rep_i9 _value_i9 h_233 h_196
          have _selected_domain : M.mem (Litex.denote _value_i9) ((_object_i11 (M := M))).val.signature.domain := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) _litex_input) (Litex.denote _value_i9)).mpr ⟨h_233, (Eq.mpr rfl (h_196 : (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) (Litex.denote _value_i9)))⟩
          exact Eq.mp rfl (Litex.selectedFn_call_spec (_object_i11 (M := M)) (Litex.denote _value_i9) _selected_domain).2)
      )
  )

theorem h_269 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_233 : M.mem (Litex.denote _value_i9) (M.standard Litex.StandardSetValue.real)) {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (_membership_i12 : M.mem (Litex.denote _value_i12) (M.standard Litex.StandardSetValue.real)) (h_196 : (¬ ((Litex.denote _value_i9) = (M.number (0 : ℂ))))) (h_267 : ((Litex.denote _value_i12) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)))), ((Litex.denote _value_i12) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.denote _value_i9))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i9 _rep_i9 _value_i9 h_233 _Host_i12 _rep_i12 _value_i12 _membership_i12 h_196 h_267
          have _selected_domain : M.mem (Litex.denote _value_i9) ((_object_i11 (M := M))).val.signature.domain := (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.real) (Litex.denote (Litex.R (M := M))) (M.standard_isSet Litex.StandardSetValue.real) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) _litex_input) (Litex.denote _value_i9)).mpr ⟨h_233, (Eq.mpr rfl (h_196 : (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) (Litex.denote _value_i9)))⟩
          apply Litex.selectedFn_unique (_object_i11 (M := M)) (Litex.denote _value_i9) (Litex.denote _value_i12) _selected_domain
          refine ⟨_membership_i12, ?_⟩
          exact Eq.mpr rfl (h_267 : ((Litex.denote _value_i12) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i9)))))
      )
  )

noncomputable def _object_w20 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i9 : M.Value) => (¬ (_raw_i9 = (M.number (0 : ℂ))))) (_object_i11 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_230 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

noncomputable def _object_w21 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_270 : (by
  let _equal_wd_1_0 := (_object_w20 (M := M))
  let _equal_wd_1_1 := (_object_w21 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_402 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
          have h_405 : ¬ Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
            (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))
          exact (Eq.trans (Eq.symm (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i11 (M := M))) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))))) (Eq.trans ((h_232 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_402 h_405) (congrArg₂ M.divValue (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_selected_x5f_reciprocal_x5f_function_x2f_statement_x2e_lit
