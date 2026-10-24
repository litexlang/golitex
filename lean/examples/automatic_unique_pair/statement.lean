import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_automatic_x5f_unique_x5f_pair_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_8 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_9 : Litex.In _value_i2 (Litex.R (M := M))), (∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_10 : Litex.In _value_i3 (Litex.R (M := M))), ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_11 : Litex.In _value_i4 (Litex.R (M := M))), ∃ (h_1 : Litex.Same _value_i3 _value_i1), Litex.Same _value_i4 _value_i2) ∧ (∀ (_unique_left_i3 : Litex.Obj (M := M) M.Value) (_member_left_i3 : M.mem (Litex.denote _unique_left_i3) (M.standard Litex.StandardSetValue.real)) (_unique_left_i4 : Litex.Obj (M := M) M.Value) (_member_left_i4 : M.mem (Litex.denote _unique_left_i4) (M.standard Litex.StandardSetValue.real)) (_unique_right_i3 : Litex.Obj (M := M) M.Value) (_member_right_i3 : M.mem (Litex.denote _unique_right_i3) (M.standard Litex.StandardSetValue.real)) (_unique_right_i4 : Litex.Obj (M := M) M.Value) (_member_right_i4 : M.mem (Litex.denote _unique_right_i4) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i3) = (Litex.denote _value_i1))) (_body_right_0 : ((Litex.denote _unique_right_i3) = (Litex.denote _value_i1))) (_body_left_1 : ((Litex.denote _unique_left_i4) = (Litex.denote _value_i2))) (_body_right_1 : ((Litex.denote _unique_right_i4) = (Litex.denote _value_i2))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i3), (Litex.denote _unique_left_i4)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i3), (Litex.denote _unique_right_i4)])) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_8 _Host_i2 _rep_i2 _value_i2 h_9
          have h_12 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_13 : Litex.In _value_i2 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_7 : (∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (h_14 : Litex.In _value_i5 (Litex.R (M := M))), ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_15 : Litex.In _value_i6 (Litex.R (M := M))), ∃ (h_5 : Litex.Same _value_i5 _value_i1), Litex.Same _value_i6 _value_i2) ∧ (∀ (_unique_left_i5 : Litex.Obj (M := M) M.Value) (_member_left_i5 : M.mem (Litex.denote _unique_left_i5) (M.standard Litex.StandardSetValue.real)) (_unique_left_i6 : Litex.Obj (M := M) M.Value) (_member_left_i6 : M.mem (Litex.denote _unique_left_i6) (M.standard Litex.StandardSetValue.real)) (_unique_right_i5 : Litex.Obj (M := M) M.Value) (_member_right_i5 : M.mem (Litex.denote _unique_right_i5) (M.standard Litex.StandardSetValue.real)) (_unique_right_i6 : Litex.Obj (M := M) M.Value) (_member_right_i6 : M.mem (Litex.denote _unique_right_i6) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i5) = (Litex.denote _value_i1))) (_body_right_0 : ((Litex.denote _unique_right_i5) = (Litex.denote _value_i1))) (_body_left_1 : ((Litex.denote _unique_left_i6) = (Litex.denote _value_i2))) (_body_right_1 : ((Litex.denote _unique_right_i6) = (Litex.denote _value_i2))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i5), (Litex.denote _unique_left_i6)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i5), (Litex.denote _unique_right_i6)])) :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i5 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1)
                    have h_28 : Litex.In _value_i5 (Litex.R (M := M)) := h_12
                    let _value_i6 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote _value_i2) (Litex.isSet _value_i2)
                    have h_29 : Litex.In _value_i6 (Litex.R (M := M)) := h_13
                    have h_30 : Litex.Same _value_i5 _value_i1 := rfl
                    have h_31 : Litex.Same _value_i6 _value_i2 := rfl
                    have h_32 : Litex.Same _value_i1 _value_i1 := (show @Eq M.Value _ _ from Eq.refl _)
                    have h_34 : Litex.Same _value_i2 _value_i2 := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ⟨⟨_value_i5, h_28, _value_i6, h_29, h_32, h_34⟩, (by
                      intro _unique_left_i5 _member_left_i5 _unique_left_i6 _member_left_i6 _unique_right_i5 _member_right_i5 _unique_right_i6 _member_right_i6 _body_left_0 _body_right_0 _body_left_1 _body_right_1
                      exact (show ∀ {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_66 : Litex.In _value_i8 (Litex.R (M := M))) {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_67 : Litex.In _value_i10 (Litex.R (M := M))) {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_68 : Litex.In _value_i9 (Litex.R (M := M))) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_69 : Litex.In _value_i11 (Litex.R (M := M))) (h_36 : Litex.Same _value_i8 _value_i1) (h_37 : Litex.Same _value_i9 _value_i1) (h_38 : Litex.Same _value_i10 _value_i2) (h_39 : Litex.Same _value_i11 _value_i2), (by
                      let _object_w3 := (Litex.tuple (M := M) ![Litex.denote _value_i8, Litex.denote _value_i10] (Fin.cases (Litex.isSet _value_i8) (Fin.cases (Litex.isSet _value_i10) (fun i => Fin.elim0 i))))
                      let _object_w4 := (Litex.tuple (M := M) ![Litex.denote _value_i9, Litex.denote _value_i11] (Fin.cases (Litex.isSet _value_i9) (Fin.cases (Litex.isSet _value_i11) (fun i => Fin.elim0 i))))
                      exact (by
                        let _equal_wd_1_0 := _object_w3
                        let _equal_wd_1_1 := _object_w4
                        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
                    ) from (by
                      intro _Host_i8 _rep_i8 _value_i8 h_66 _Host_i10 _rep_i10 _value_i10 h_67 _Host_i9 _rep_i9 _value_i9 h_68 _Host_i11 _rep_i11 _value_i11 h_69 h_36 h_37 h_38 h_39
                      let _object_w3 := (Litex.tuple (M := M) ![Litex.denote _value_i8, Litex.denote _value_i10] (Fin.cases (Litex.isSet _value_i8) (Fin.cases (Litex.isSet _value_i10) (fun i => Fin.elim0 i))))
                      let _object_w4 := (Litex.tuple (M := M) ![Litex.denote _value_i9, Litex.denote _value_i11] (Fin.cases (Litex.isSet _value_i9) (Fin.cases (Litex.isSet _value_i11) (fun i => Fin.elim0 i))))
                      have h_40 : (by
                        let _equal_wd_1_0 := _object_w3
                        let _equal_wd_1_1 := _object_w4
                        exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (congrArg (Litex.FiniteFunction.tupleValue (M := M)) (funext (by
                                have _finiteProof_0 := (((h_36).trans (h_37).symm))
                                have _finiteProof_1 := (((h_38).trans (h_39).symm))
                                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                              )))
                            )
                        )
                      exact h_40
                    )) _unique_left_i5 _member_left_i5 _unique_left_i6 _member_left_i6 _unique_right_i5 _member_right_i5 _unique_right_i6 _member_right_i6 _body_left_0 _body_right_0 _body_left_1 _body_right_1)⟩
                )
            )

          have h_82 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (_membership_i12 : M.mem (Litex.denote _value_i12) (M.standard Litex.StandardSetValue.real)) {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (_membership_i14 : M.mem (Litex.denote _value_i14) (M.standard Litex.StandardSetValue.real)) {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (_membership_i13 : M.mem (Litex.denote _value_i13) (M.standard Litex.StandardSetValue.real)) {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (_membership_i15 : M.mem (Litex.denote _value_i15) (M.standard Litex.StandardSetValue.real)) (h_75 : ((Litex.denote _value_i12) = (Litex.denote _value_i1))) (h_76 : ((Litex.denote _value_i13) = (Litex.denote _value_i1))) (h_77 : ((Litex.denote _value_i14) = (Litex.denote _value_i2))) (h_78 : ((Litex.denote _value_i15) = (Litex.denote _value_i2))), ((((Litex.denote _value_i12) = (Litex.denote _value_i13))) ∧ (((Litex.denote _value_i14) = (Litex.denote _value_i15)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i12 _rep_i12 _value_i12 _membership_i12 _Host_i14 _rep_i14 _value_i14 _membership_i14 _Host_i13 _rep_i13 _value_i13 _membership_i13 _Host_i15 _rep_i15 _value_i15 _membership_i15 h_75 h_76 h_77 h_78
                    have _unique : ∀ (_unique_left_i5 : Litex.Obj (M := M) M.Value) (_member_left_i5 : M.mem (Litex.denote _unique_left_i5) (M.standard Litex.StandardSetValue.real)) (_unique_left_i6 : Litex.Obj (M := M) M.Value) (_member_left_i6 : M.mem (Litex.denote _unique_left_i6) (M.standard Litex.StandardSetValue.real)) (_unique_right_i5 : Litex.Obj (M := M) M.Value) (_member_right_i5 : M.mem (Litex.denote _unique_right_i5) (M.standard Litex.StandardSetValue.real)) (_unique_right_i6 : Litex.Obj (M := M) M.Value) (_member_right_i6 : M.mem (Litex.denote _unique_right_i6) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i5) = (Litex.denote _value_i1))) (_body_right_0 : ((Litex.denote _unique_right_i5) = (Litex.denote _value_i1))) (_body_left_1 : ((Litex.denote _unique_left_i6) = (Litex.denote _value_i2))) (_body_right_1 : ((Litex.denote _unique_right_i6) = (Litex.denote _value_i2))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i5), (Litex.denote _unique_left_i6)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i5), (Litex.denote _unique_right_i6)]) := (h_7).2
                    have _same := _unique (Litex.semanticObject (Litex.denote _value_i12) (Litex.isSet _value_i12)) _membership_i12 (Litex.semanticObject (Litex.denote _value_i14) (Litex.isSet _value_i14)) _membership_i14 (Litex.semanticObject (Litex.denote _value_i13) (Litex.isSet _value_i13)) _membership_i13 (Litex.semanticObject (Litex.denote _value_i15) (Litex.isSet _value_i15)) _membership_i15 h_75 h_76 h_77 h_78
                    exact ⟨(by simpa only [Litex.FiniteFunction.call_tuple, Matrix.cons_val_zero, Matrix.cons_val_succ, Litex.semanticObject_denote] using congrArg (fun t => Litex.FunctionSemantics.callValue (M := M) t (Litex.FiniteFunction.index (0 : Fin 2))) _same), (by simpa only [Litex.FiniteFunction.call_tuple, Matrix.cons_val_zero, Matrix.cons_val_succ, Litex.semanticObject_denote] using congrArg (fun t => Litex.FunctionSemantics.callValue (M := M) t (Litex.FiniteFunction.index (Fin.succ (0 : Fin 1)))) _same)⟩)
                )
            )
          exact h_7
        )
      )
  )

theorem h_91 : (∃ (_value_i16 : Litex.Obj (M := M) M.Value), ∃ (h_92 : Litex.In _value_i16 (Litex.R (M := M))), ∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_93 : Litex.In _value_i17 (Litex.R (M := M))), ∃ (h_89 : Litex.Same _value_i16 (Litex.number (M := M) (2 : ℂ))), Litex.Same _value_i17 (Litex.number (M := M) (3 : ℂ))) ∧ (∀ (_unique_left_i16 : Litex.Obj (M := M) M.Value) (_member_left_i16 : M.mem (Litex.denote _unique_left_i16) (M.standard Litex.StandardSetValue.real)) (_unique_left_i17 : Litex.Obj (M := M) M.Value) (_member_left_i17 : M.mem (Litex.denote _unique_left_i17) (M.standard Litex.StandardSetValue.real)) (_unique_right_i16 : Litex.Obj (M := M) M.Value) (_member_right_i16 : M.mem (Litex.denote _unique_right_i16) (M.standard Litex.StandardSetValue.real)) (_unique_right_i17 : Litex.Obj (M := M) M.Value) (_member_right_i17 : M.mem (Litex.denote _unique_right_i17) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i16) = (M.number (2 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i16) = (M.number (2 : ℂ)))) (_body_left_1 : ((Litex.denote _unique_left_i17) = (M.number (3 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i17) = (M.number (3 : ℂ)))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i16), (Litex.denote _unique_left_i17)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i16), (Litex.denote _unique_right_i17)])) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_101 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
          have h_102 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) :=
            (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))
          rcases ((h_4 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_101 (Litex.number (M := M) (3 : ℂ)) h_102) with ⟨_known_exists, _known_unique⟩
          rcases _known_exists with ⟨_value_i16, h_92, _value_i17, h_93, h_89, h_90⟩
          have _exist_match_0 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.sameRefl (Litex.R (M := M)))
          have _exist_match_1 : Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (2 : ℂ)))
          have _exist_match_2 : Litex.Same (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (3 : ℂ)))
          exact ⟨⟨_value_i16, h_92, _value_i17, h_93, h_89, h_90⟩, _known_unique⟩
        )
      )
  )

theorem h_110 : ∀ {_Host_i18 : Type _} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (_membership_i18 : M.mem (Litex.denote _value_i18) (M.standard Litex.StandardSetValue.real)) {_Host_i20 : Type _} [_rep_i20 : Litex.Representation M _Host_i20] (_value_i20 : Litex.Obj (M := M) _Host_i20) (_membership_i20 : M.mem (Litex.denote _value_i20) (M.standard Litex.StandardSetValue.real)) {_Host_i19 : Type _} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (_membership_i19 : M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) {_Host_i21 : Type _} [_rep_i21 : Litex.Representation M _Host_i21] (_value_i21 : Litex.Obj (M := M) _Host_i21) (_membership_i21 : M.mem (Litex.denote _value_i21) (M.standard Litex.StandardSetValue.real)) (h_103 : ((Litex.denote _value_i18) = (M.number (2 : ℂ)))) (h_104 : ((Litex.denote _value_i19) = (M.number (2 : ℂ)))) (h_105 : ((Litex.denote _value_i20) = (M.number (3 : ℂ)))) (h_106 : ((Litex.denote _value_i21) = (M.number (3 : ℂ)))), ((((Litex.denote _value_i18) = (Litex.denote _value_i19))) ∧ (((Litex.denote _value_i20) = (Litex.denote _value_i21)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i18 _rep_i18 _value_i18 _membership_i18 _Host_i20 _rep_i20 _value_i20 _membership_i20 _Host_i19 _rep_i19 _value_i19 _membership_i19 _Host_i21 _rep_i21 _value_i21 _membership_i21 h_103 h_104 h_105 h_106
          have _unique : ∀ (_unique_left_i16 : Litex.Obj (M := M) M.Value) (_member_left_i16 : M.mem (Litex.denote _unique_left_i16) (M.standard Litex.StandardSetValue.real)) (_unique_left_i17 : Litex.Obj (M := M) M.Value) (_member_left_i17 : M.mem (Litex.denote _unique_left_i17) (M.standard Litex.StandardSetValue.real)) (_unique_right_i16 : Litex.Obj (M := M) M.Value) (_member_right_i16 : M.mem (Litex.denote _unique_right_i16) (M.standard Litex.StandardSetValue.real)) (_unique_right_i17 : Litex.Obj (M := M) M.Value) (_member_right_i17 : M.mem (Litex.denote _unique_right_i17) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i16) = (M.number (2 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i16) = (M.number (2 : ℂ)))) (_body_left_1 : ((Litex.denote _unique_left_i17) = (M.number (3 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i17) = (M.number (3 : ℂ)))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i16), (Litex.denote _unique_left_i17)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i16), (Litex.denote _unique_right_i17)]) := ((h_91 (M := M))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i18) (Litex.isSet _value_i18)) _membership_i18 (Litex.semanticObject (Litex.denote _value_i20) (Litex.isSet _value_i20)) _membership_i20 (Litex.semanticObject (Litex.denote _value_i19) (Litex.isSet _value_i19)) _membership_i19 (Litex.semanticObject (Litex.denote _value_i21) (Litex.isSet _value_i21)) _membership_i21 h_103 h_104 h_105 h_106
          exact ⟨(by simpa only [Litex.FiniteFunction.call_tuple, Matrix.cons_val_zero, Matrix.cons_val_succ, Litex.semanticObject_denote] using congrArg (fun t => Litex.FunctionSemantics.callValue (M := M) t (Litex.FiniteFunction.index (0 : Fin 2))) _same), (by simpa only [Litex.FiniteFunction.call_tuple, Matrix.cons_val_zero, Matrix.cons_val_succ, Litex.semanticObject_denote] using congrArg (fun t => Litex.FunctionSemantics.callValue (M := M) t (Litex.FiniteFunction.index (Fin.succ (0 : Fin 1)))) _same)⟩)
      )
  )

theorem h_113 : ∃ (_value_i22 : Litex.Obj (M := M) M.Value), ∃ (h_114 : Litex.In _value_i22 (Litex.R (M := M))), ∃ (_value_i23 : Litex.Obj (M := M) M.Value), ∃ (h_115 : Litex.In _value_i23 (Litex.R (M := M))), ∃ (h_111 : Litex.Same _value_i22 (Litex.number (M := M) (2 : ℂ))), Litex.Same _value_i23 (Litex.number (M := M) (3 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        ((h_91 (M := M))).1
      )
  )

theorem h_118 : ∃ (_value_i24 : Litex.Obj (M := M) M.Value), ∃ (h_119 : Litex.In _value_i24 (Litex.R (M := M))), ∃ (_value_i25 : Litex.Obj (M := M) M.Value), ∃ (h_120 : Litex.In _value_i25 (Litex.R (M := M))), ∃ (h_116 : Litex.Same _value_i24 (Litex.number (M := M) (4 : ℂ))), Litex.Same _value_i25 (Litex.number (M := M) (5 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_128 : Litex.In (Litex.number (M := M) (4 : ℂ)) (Litex.R (M := M)) :=
            (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))
          have h_129 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.R (M := M)) :=
            (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))
          rcases (((h_4 (M := M)) (Litex.number (M := M) (4 : ℂ)) h_128 (Litex.number (M := M) (5 : ℂ)) h_129)).1 with ⟨_value_i24, h_119, _value_i25, h_120, h_116, h_117⟩
          have _exist_match_0 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.sameRefl (Litex.R (M := M)))
          have _exist_match_1 : Litex.Same (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (4 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (4 : ℂ)))
          have _exist_match_2 : Litex.Same (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (5 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (5 : ℂ)))
          exact ⟨_value_i24, h_119, _value_i25, h_120, h_116, h_117⟩
        )
      )
  )

noncomputable def _value_i28 : Litex.Obj (M := M) M.Value :=
  Classical.choose ((show ∃ (_value_i26 : Litex.Obj (M := M) M.Value), ∃ (h_133 : Litex.In _value_i26 (Litex.R (M := M))), ∃ (_value_i27 : Litex.Obj (M := M) M.Value), ∃ (h_134 : Litex.In _value_i27 (Litex.R (M := M))), ∃ (h_130 : Litex.Same _value_i26 (Litex.number (M := M) (4 : ℂ))), Litex.Same _value_i27 (Litex.number (M := M) (5 : ℂ)) from (h_118 (M := M))))

theorem h_135 : Litex.In (_value_i28 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((show ∃ (_value_i26 : Litex.Obj (M := M) M.Value), ∃ (h_133 : Litex.In _value_i26 (Litex.R (M := M))), ∃ (_value_i27 : Litex.Obj (M := M) M.Value), ∃ (h_134 : Litex.In _value_i27 (Litex.R (M := M))), ∃ (h_130 : Litex.Same _value_i26 (Litex.number (M := M) (4 : ℂ))), Litex.Same _value_i27 (Litex.number (M := M) (5 : ℂ)) from (h_118 (M := M)))))))
      )
  )

noncomputable def _value_i29 : Litex.Obj (M := M) M.Value :=
  Classical.choose ((Classical.choose_spec ((Classical.choose_spec ((show ∃ (_value_i26 : Litex.Obj (M := M) M.Value), ∃ (h_133 : Litex.In _value_i26 (Litex.R (M := M))), ∃ (_value_i27 : Litex.Obj (M := M) M.Value), ∃ (h_134 : Litex.In _value_i27 (Litex.R (M := M))), ∃ (h_130 : Litex.Same _value_i26 (Litex.number (M := M) (4 : ℂ))), Litex.Same _value_i27 (Litex.number (M := M) (5 : ℂ)) from (h_118 (M := M))))))))

theorem h_136 : Litex.In (_value_i29 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((show ∃ (_value_i26 : Litex.Obj (M := M) M.Value), ∃ (h_133 : Litex.In _value_i26 (Litex.R (M := M))), ∃ (_value_i27 : Litex.Obj (M := M) M.Value), ∃ (h_134 : Litex.In _value_i27 (Litex.R (M := M))), ∃ (h_130 : Litex.Same _value_i26 (Litex.number (M := M) (4 : ℂ))), Litex.Same _value_i27 (Litex.number (M := M) (5 : ℂ)) from (h_118 (M := M)))))))))))
      )
  )

theorem h_137 : Litex.Same (_value_i28 (M := M)) (Litex.number (M := M) (4 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((show ∃ (_value_i26 : Litex.Obj (M := M) M.Value), ∃ (h_133 : Litex.In _value_i26 (Litex.R (M := M))), ∃ (_value_i27 : Litex.Obj (M := M) M.Value), ∃ (h_134 : Litex.In _value_i27 (Litex.R (M := M))), ∃ (h_130 : Litex.Same _value_i26 (Litex.number (M := M) (4 : ℂ))), Litex.Same _value_i27 (Litex.number (M := M) (5 : ℂ)) from (h_118 (M := M)))))))))))))
      )
  )

theorem h_138 : Litex.Same (_value_i29 (M := M)) (Litex.number (M := M) (5 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((show ∃ (_value_i26 : Litex.Obj (M := M) M.Value), ∃ (h_133 : Litex.In _value_i26 (Litex.R (M := M))), ∃ (_value_i27 : Litex.Obj (M := M) M.Value), ∃ (h_134 : Litex.In _value_i27 (Litex.R (M := M))), ∃ (h_130 : Litex.Same _value_i26 (Litex.number (M := M) (4 : ℂ))), Litex.Same _value_i27 (Litex.number (M := M) (5 : ℂ)) from (h_118 (M := M)))))))))))))
      )
  )

theorem h_139 : Litex.Same (_value_i28 (M := M)) (Litex.number (M := M) (4 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (h_137 (M := M))
      )
  )

theorem h_141 : Litex.Same (_value_i29 (M := M)) (Litex.number (M := M) (5 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (h_138 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_automatic_x5f_unique_x5f_pair_x2f_statement_x2e_lit
