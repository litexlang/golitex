import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_selected_x5f_sum_x5f_function_x2f_statement_x2e_lit

universe u v1 v2 v10 v11 v14
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_7 : Litex.In _value_i2 (Litex.R (M := M))), (∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_8 : Litex.In _value_i3 (Litex.R (M := M))), Litex.Same _value_i3 (Litex.add _value_i1 _value_i2 (M.real_subset_complex _ h_6) (M.real_subset_complex _ h_7))) ∧ (∀ (_unique_left_i3 : Litex.Obj (M := M) M.Value) (_member_left_i3 : M.mem (Litex.denote _unique_left_i3) (M.standard Litex.StandardSetValue.real)) (_unique_right_i3 : Litex.Obj (M := M) M.Value) (_member_right_i3 : M.mem (Litex.denote _unique_right_i3) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i3) = (M.addValue (Litex.denote _value_i1) (Litex.denote _value_i2)))) (_body_right_0 : ((Litex.denote _unique_right_i3) = (M.addValue (Litex.denote _value_i1) (Litex.denote _value_i2)))), (Litex.denote _unique_left_i3) = (Litex.denote _unique_right_i3)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 _Host_i2 _rep_i2 _value_i2 h_7
          have h_44 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_45 : Litex.In _value_i2 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          have h_5 : (∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_46 : Litex.In _value_i4 (Litex.R (M := M))), Litex.Same _value_i4 (Litex.add _value_i1 _value_i2 (M.real_subset_complex _ h_44) (M.real_subset_complex _ h_45))) ∧ (∀ (_unique_left_i4 : Litex.Obj (M := M) M.Value) (_member_left_i4 : M.mem (Litex.denote _unique_left_i4) (M.standard Litex.StandardSetValue.real)) (_unique_right_i4 : Litex.Obj (M := M) M.Value) (_member_right_i4 : M.mem (Litex.denote _unique_right_i4) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i4) = (M.addValue (Litex.denote _value_i1) (Litex.denote _value_i2)))) (_body_right_0 : ((Litex.denote _unique_right_i4) = (M.addValue (Litex.denote _value_i1) (Litex.denote _value_i2)))), (Litex.denote _unique_left_i4) = (Litex.denote _unique_right_i4)) :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i4 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.add _value_i1 _value_i2 (M.real_subset_complex _ h_44) (M.real_subset_complex _ h_45))) (Litex.isSet (Litex.add _value_i1 _value_i2 (M.real_subset_complex _ h_44) (M.real_subset_complex _ h_45)))
                    have h_153 : Litex.In _value_i4 (Litex.R (M := M)) := (by
                      let _atomic_wd_1_0 := (Litex.add _value_i1 _value_i2 (M.real_subset_complex _ h_44) (M.real_subset_complex _ h_45))
                      exact (Litex.addInR _value_i1 _value_i2 h_44 h_45))
                    have h_154 : Litex.Same _value_i4 (Litex.add _value_i1 _value_i2 (M.real_subset_complex _ h_44) (M.real_subset_complex _ h_45)) := rfl
                    have h_155 : (by
                      let _equal_wd_1_0 := (Litex.add _value_i1 _value_i2 (M.real_subset_complex _ h_44) (M.real_subset_complex _ h_45))
                      let _equal_wd_1_1 := _equal_wd_1_0
                      exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ⟨⟨_value_i4, h_153, h_155⟩, (by
                      intro _unique_left_i4 _member_left_i4 _unique_right_i4 _member_right_i4 _body_left_0 _body_right_0
                      exact (show ∀ {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_185 : Litex.In _value_i6 (Litex.R (M := M))) {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_186 : Litex.In _value_i7 (Litex.R (M := M))) (h_157 : (by
                      let _equal_wd_1_1 := (Litex.add _value_i1 _value_i2 (M.real_subset_complex _ h_44) (M.real_subset_complex _ h_45))
                      exact Litex.Same _value_i6 _equal_wd_1_1)) (h_158 : (by
                      let _equal_wd_1_1 := (Litex.add _value_i1 _value_i2 (M.real_subset_complex _ h_44) (M.real_subset_complex _ h_45))
                      exact Litex.Same _value_i7 _equal_wd_1_1)), Litex.Same _value_i6 _value_i7 from (by
                      intro _Host_i6 _rep_i6 _value_i6 h_185 _Host_i7 _rep_i7 _value_i7 h_186 h_157 h_158
                      have h_159 : Litex.Same _value_i6 _value_i7 :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((h_157).trans (h_158).symm)
                            )
                        )
                      exact h_159
                    )) _unique_left_i4 _member_left_i4 _unique_right_i4 _member_right_i4 _body_left_0 _body_right_0)⟩
                )
            )

          have h_191 : ∀ {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (_membership_i8 : M.mem (Litex.denote _value_i8) (M.standard Litex.StandardSetValue.real)) {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (_membership_i9 : M.mem (Litex.denote _value_i9) (M.standard Litex.StandardSetValue.real)) (h_188 : ((Litex.denote _value_i8) = (M.addValue (Litex.denote _value_i1) (Litex.denote _value_i2)))) (h_189 : ((Litex.denote _value_i9) = (M.addValue (Litex.denote _value_i1) (Litex.denote _value_i2)))), ((Litex.denote _value_i8) = (Litex.denote _value_i9)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i8 _rep_i8 _value_i8 _membership_i8 _Host_i9 _rep_i9 _value_i9 _membership_i9 h_188 h_189
                    have _unique : ∀ (_unique_left_i4 : Litex.Obj (M := M) M.Value) (_member_left_i4 : M.mem (Litex.denote _unique_left_i4) (M.standard Litex.StandardSetValue.real)) (_unique_right_i4 : Litex.Obj (M := M) M.Value) (_member_right_i4 : M.mem (Litex.denote _unique_right_i4) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i4) = (M.addValue (Litex.denote _value_i1) (Litex.denote _value_i2)))) (_body_right_0 : ((Litex.denote _unique_right_i4) = (M.addValue (Litex.denote _value_i1) (Litex.denote _value_i2)))), (Litex.denote _unique_left_i4) = (Litex.denote _unique_right_i4) := (h_5).2
                    have _same := _unique (Litex.semanticObject (Litex.denote _value_i8) (Litex.isSet _value_i8)) _membership_i8 (Litex.semanticObject (Litex.denote _value_i9) (Litex.isSet _value_i9)) _membership_i9 h_188 h_189
                    exact _same)
                )
            )
          exact h_5
        )
      )
  )

noncomputable def _object_i13 := (show Litex.Obj (M := M) (Litex.SelectedFn M) from by
  let _selected_signature := ((show Litex.Obj (M := M) (Litex.FunctionSignature M) from (by
  have _checked_header : ∀ (_raw_i10 : M.Value) (_raw_i11 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True) _raw_i10 _raw_i11) → True := by
    intro _raw_i10 _raw_i11 h_309 h_310 _
    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_309)
    have h_309 : Litex.In _value_i10 (Litex.R (M := M)) := h_309
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_310)
    have h_310 : Litex.In _value_i11 (Litex.R (M := M)) := h_310
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.two (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True))))).val
  have _selected_pointwise : ∀ (_raw_i10 : M.Value) (_raw_i11 : M.Value), M.mem _raw_i10 (M.standard Litex.StandardSetValue.real) → M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True) _raw_i10 _raw_i11) → ∃! _selected_output : M.Value, M.mem _selected_output (Litex.denote (Litex.R (M := M))) ∧ ((_selected_output = (M.addValue _raw_i10 _raw_i11))) := (by
    intro _raw_i10 _raw_i11 h_309 h_310 _
    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_309)
    have h_309 : Litex.In _value_i10 (Litex.R (M := M)) := h_309
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_310)
    have h_310 : Litex.In _value_i11 (Litex.R (M := M)) := h_310
    have h_268 : ∀ {_Host_i10 : Type u} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_271 : Litex.In _value_i10 (Litex.R (M := M))) {_Host_i11 : Type u} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_272 : Litex.In _value_i11 (Litex.R (M := M))), (∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_273 : Litex.In _value_i12 (Litex.R (M := M))), Litex.Same _value_i12 (Litex.add _value_i10 _value_i11 (M.real_subset_complex _ h_271) (M.real_subset_complex _ h_272))) ∧ (∀ (_unique_left_i12 : Litex.Obj (M := M) M.Value) (_member_left_i12 : M.mem (Litex.denote _unique_left_i12) (M.standard Litex.StandardSetValue.real)) (_unique_right_i12 : Litex.Obj (M := M) M.Value) (_member_right_i12 : M.mem (Litex.denote _unique_right_i12) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i12) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11)))) (_body_right_0 : ((Litex.denote _unique_right_i12) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11)))), (Litex.denote _unique_left_i12) = (Litex.denote _unique_right_i12)) := (by
      intro _Host_i10 _rep_i10 _value_i10 h_271 _Host_i11 _rep_i11 _value_i11 h_272
      exact ((h_3 (M := M)) _value_i10 h_271 _value_i11 h_272)
    )
    obtain ⟨_selected_exists, _selected_unique⟩ := h_268 _value_i10 h_309 _value_i11 h_310
    apply Litex.existsUniqueValueOfObjects (Litex.denote (Litex.R (M := M))) (fun _selected_output => (_selected_output = (M.addValue _raw_i10 _raw_i11)))
    · obtain ⟨_selected_witness, _selected_member, _selected_clause_0⟩ := _selected_exists
      exact ⟨_selected_witness, _selected_member, _selected_clause_0⟩
    · intro _selected_left _selected_right _selected_left_member _selected_right_member _selected_left_body _selected_right_body
      exact _selected_unique _selected_left _selected_left_member _selected_right _selected_right_member _selected_left_body _selected_right_body)
  exact Litex.selectedFn _selected_signature (fun (_selected_input _selected_output : M.Value) => (_selected_output = (M.addValue (Litex.FunctionSemantics.callValue (M := M) _selected_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _selected_input (M.number (2 : ℂ)))))) (by
    intro _selected_input _selected_domain
    obtain ⟨_selected_members, _selected_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
  have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
  have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _selected_input).mp _selected_domain
    exact _selected_pointwise (Litex.FunctionSemantics.callValue (M := M) _selected_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _selected_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _selected_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _selected_members (1 : Fin 2)) _selected_guard))

theorem h_311 : Litex.In (_object_i13 (M := M)) (Litex.fnSet ((_object_i13 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.selectedFnInFnSet (_object_i13 (M := M)))
      )
  )

theorem h_313 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_314 : M.mem (Litex.denote _value_i10) (M.standard Litex.StandardSetValue.real)) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_315 : M.mem (Litex.denote _value_i11) (M.standard Litex.StandardSetValue.real)), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i13 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i10 _rep_i10 _value_i10 h_314 _Host_i11 _rep_i11 _value_i11 h_315
          have _selected_domain : M.mem (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)]) ((_object_i13 (M := M))).val.signature.domain := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
            have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
            have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])).mpr ⟨(Litex.FiniteFunction.tuple_inCart ![(Litex.denote _value_i10), (Litex.denote _value_i11)] ![M.standard Litex.StandardSetValue.real, M.standard Litex.StandardSetValue.real] (by
            have _finiteProof_0 := (h_314)
            have _finiteProof_1 := (h_315)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )), (Eq.mpr (congrArg₂ (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i10), (Litex.denote _value_i11)]) (M.number (1 : ℂ)) = (Litex.denote _value_i10) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i10), (Litex.denote _value_i11)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i10), (Litex.denote _value_i11)]) (M.number (2 : ℂ)) = (Litex.denote _value_i11) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i10), (Litex.denote _value_i11)] (1 : Fin 2))) (True.intro : (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True) (Litex.denote _value_i10) (Litex.denote _value_i11)))⟩
          exact Eq.mp (congrArg₂ (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => ((Litex.FunctionSemantics.callValue (Litex.denote (_object_i13 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])) = (M.addValue _raw_i10 _raw_i11))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i10), (Litex.denote _value_i11)]) (M.number (1 : ℂ)) = (Litex.denote _value_i10) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i10), (Litex.denote _value_i11)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i10), (Litex.denote _value_i11)]) (M.number (2 : ℂ)) = (Litex.denote _value_i11) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i10), (Litex.denote _value_i11)] (1 : Fin 2))) (Litex.selectedFn_call_spec (_object_i13 (M := M)) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)]) _selected_domain).2)
      )
  )

theorem h_363 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_314 : M.mem (Litex.denote _value_i10) (M.standard Litex.StandardSetValue.real)) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_315 : M.mem (Litex.denote _value_i11) (M.standard Litex.StandardSetValue.real)) {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (_membership_i14 : M.mem (Litex.denote _value_i14) (M.standard Litex.StandardSetValue.real)) (h_361 : ((Litex.denote _value_i14) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11)))), ((Litex.denote _value_i14) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i13 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)]))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i10 _rep_i10 _value_i10 h_314 _Host_i11 _rep_i11 _value_i11 h_315 _Host_i14 _rep_i14 _value_i14 _membership_i14 h_361
          have _selected_domain : M.mem (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)]) ((_object_i13 (M := M))).val.signature.domain := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)] (by
            have _finiteProof_0 := ((M.standard_isSet Litex.StandardSetValue.real))
            have _finiteProof_1 := ((M.standard_isSet Litex.StandardSetValue.real))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])).mpr ⟨(Litex.FiniteFunction.tuple_inCart ![(Litex.denote _value_i10), (Litex.denote _value_i11)] ![M.standard Litex.StandardSetValue.real, M.standard Litex.StandardSetValue.real] (by
            have _finiteProof_0 := (h_314)
            have _finiteProof_1 := (h_315)
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )), (Eq.mpr (congrArg₂ (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i10), (Litex.denote _value_i11)]) (M.number (1 : ℂ)) = (Litex.denote _value_i10) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i10), (Litex.denote _value_i11)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i10), (Litex.denote _value_i11)]) (M.number (2 : ℂ)) = (Litex.denote _value_i11) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i10), (Litex.denote _value_i11)] (1 : Fin 2))) (True.intro : (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True) (Litex.denote _value_i10) (Litex.denote _value_i11)))⟩
          apply Litex.selectedFn_unique (_object_i13 (M := M)) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)]) (Litex.denote _value_i14) _selected_domain
          refine ⟨_membership_i14, ?_⟩
          exact Eq.mpr (congrArg₂ (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => ((Litex.denote _value_i14) = (M.addValue _raw_i10 _raw_i11))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i10), (Litex.denote _value_i11)]) (M.number (1 : ℂ)) = (Litex.denote _value_i10) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i10), (Litex.denote _value_i11)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i10), (Litex.denote _value_i11)]) (M.number (2 : ℂ)) = (Litex.denote _value_i11) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i10), (Litex.denote _value_i11)] (1 : Fin 2))) (h_361 : ((Litex.denote _value_i14) = (M.addValue (Litex.denote _value_i10) (Litex.denote _value_i11)))))
      )
  )

noncomputable def _object_w14 := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i10 : M.Value) (_raw_i11 : M.Value) => True) (_object_i13 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (h_311 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) True.intro)

theorem h_364 : (by
  let _equal_wd_1_0 := (_object_w14 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_395 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
          have h_398 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) :=
            (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))
          exact (Eq.trans (Eq.symm (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (Litex.sameRefl (_object_i13 (M := M))) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) (Litex.sameRefl (Litex.number (M := M) (3 : ℂ)))))) (Eq.trans ((h_313 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_395 (Litex.number (M := M) (3 : ℂ)) h_398) (Litex.NativeBridge.sameOfDenoteNumber (have h_395 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
          (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num));
        have h_398 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) :=
          (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num));
        ((fun {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_314 : Litex.In _value_i10 (Litex.R (M := M))) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_315 : Litex.In _value_i11 (Litex.R (M := M))) => (Litex.add _value_i10 _value_i11 (M.real_subset_complex _ h_314) (M.real_subset_complex _ h_315))) (Litex.number (M := M) (2 : ℂ)) h_395 (Litex.number (M := M) (3 : ℂ)) h_398)) (Litex.number (M := M) (5 : ℂ)) ((have h_395 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
          (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num));
        have h_398 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) :=
          (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num));
        ((fun {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_314 : Litex.In _value_i10 (Litex.R (M := M))) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_315 : Litex.In _value_i11 (Litex.R (M := M))) => (let _callee_object := (Litex.add _value_i10 _value_i11 (M.real_subset_complex _ h_314) (M.real_subset_complex _ h_315));
        show { _z : ℂ // Litex.denote _callee_object = M.number _z ∧ Litex.In _callee_object Litex.C } from ⟨((Litex.NativeBridge.asComplex _value_i10 (Litex.realToComplex _value_i10 h_314)) + (Litex.NativeBridge.asComplex _value_i11 (Litex.realToComplex _value_i11 h_315))), (Litex.NativeBridge.denoteAdd _value_i10 _value_i11 (M.real_subset_complex _ h_314) (M.real_subset_complex _ h_315) _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.realToComplex _value_i10 h_314)) (Litex.NativeBridge.asComplex_spec _value_i11 (Litex.realToComplex _value_i11 h_315))), (Litex.addInC _value_i10 _value_i11 (M.real_subset_complex _ h_314) (M.real_subset_complex _ h_315))⟩)) (Litex.number (M := M) (2 : ℂ)) h_395 (Litex.number (M := M) (3 : ℂ)) h_398))).val (5 : ℂ) ((have h_395 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
          (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num));
        have h_398 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) :=
          (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num));
        ((fun {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_314 : Litex.In _value_i10 (Litex.R (M := M))) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_315 : Litex.In _value_i11 (Litex.R (M := M))) => (let _callee_object := (Litex.add _value_i10 _value_i11 (M.real_subset_complex _ h_314) (M.real_subset_complex _ h_315));
        show { _z : ℂ // Litex.denote _callee_object = M.number _z ∧ Litex.In _callee_object Litex.C } from ⟨((Litex.NativeBridge.asComplex _value_i10 (Litex.realToComplex _value_i10 h_314)) + (Litex.NativeBridge.asComplex _value_i11 (Litex.realToComplex _value_i11 h_315))), (Litex.NativeBridge.denoteAdd _value_i10 _value_i11 (M.real_subset_complex _ h_314) (M.real_subset_complex _ h_315) _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.realToComplex _value_i10 h_314)) (Litex.NativeBridge.asComplex_spec _value_i11 (Litex.realToComplex _value_i11 h_315))), (Litex.addInC _value_i10 _value_i11 (M.real_subset_complex _ h_314) (M.real_subset_complex _ h_315))⟩)) (Litex.number (M := M) (2 : ℂ)) h_395 (Litex.number (M := M) (3 : ℂ)) h_398))).property.1 (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_selected_x5f_sum_x5f_function_x2f_statement_x2e_lit
