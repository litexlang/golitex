import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_real_x5f_pair_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_4 : Litex.In _value_i1 (Litex.R (M := M))), ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_5 : Litex.In _value_i2 (Litex.R (M := M))), ∃ (h_1 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ))), Litex.Same _value_i2 (Litex.number (M := M) (2 : ℂ))) ∧ (∀ (_unique_left_i1 : Litex.Obj (M := M) M.Value) (_member_left_i1 : M.mem (Litex.denote _unique_left_i1) (M.standard Litex.StandardSetValue.real)) (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.mem (Litex.denote _unique_left_i2) (M.standard Litex.StandardSetValue.real)) (_unique_right_i1 : Litex.Obj (M := M) M.Value) (_member_right_i1 : M.mem (Litex.denote _unique_right_i1) (M.standard Litex.StandardSetValue.real)) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.mem (Litex.denote _unique_right_i2) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i1) = (M.number (1 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i1) = (M.number (1 : ℂ)))) (_body_left_1 : ((Litex.denote _unique_left_i2) = (M.number (2 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i2) = (M.number (2 : ℂ)))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i1), (Litex.denote _unique_left_i2)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i1), (Litex.denote _unique_right_i2)])) :=
  (by
    litex_complete =>
      exact (
        by
          let _value_i1 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (1 : ℂ))) (Litex.isSet (Litex.number (M := M) (1 : ℂ)))
          have h_8 : Litex.In _value_i1 (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
          let _value_i2 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.isSet (Litex.number (M := M) (2 : ℂ)))
          have h_9 : Litex.In _value_i2 (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
          have h_10 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) := rfl
          have h_11 : Litex.Same _value_i2 (Litex.number (M := M) (2 : ℂ)) := rfl
          have h_12 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
          have h_14 : Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
          exact ⟨⟨_value_i1, h_8, _value_i2, h_9, h_12, h_14⟩, (by
            intro _unique_left_i1 _member_left_i1 _unique_left_i2 _member_left_i2 _unique_right_i1 _member_right_i1 _unique_right_i2 _member_right_i2 _body_left_0 _body_right_0 _body_left_1 _body_right_1
            exact (show ∀ {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_46 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_47 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_48 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_49 : Litex.In _value_i6 (Litex.R (M := M))) (h_16 : Litex.Same _value_i3 (Litex.number (M := M) (1 : ℂ))) (h_17 : Litex.Same _value_i4 (Litex.number (M := M) (1 : ℂ))) (h_18 : Litex.Same _value_i5 (Litex.number (M := M) (2 : ℂ))) (h_19 : Litex.Same _value_i6 (Litex.number (M := M) (2 : ℂ))), (by
            let _object_w7 := (Litex.tuple (M := M) ![Litex.denote _value_i3, Litex.denote _value_i5] (Fin.cases (Litex.isSet _value_i3) (Fin.cases (Litex.isSet _value_i5) (fun i => Fin.elim0 i))))
            let _object_w8 := (Litex.tuple (M := M) ![Litex.denote _value_i4, Litex.denote _value_i6] (Fin.cases (Litex.isSet _value_i4) (Fin.cases (Litex.isSet _value_i6) (fun i => Fin.elim0 i))))
            exact (by
              let _equal_wd_1_0 := _object_w7
              let _equal_wd_1_1 := _object_w8
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
          ) from (by
            intro _Host_i3 _rep_i3 _value_i3 h_46 _Host_i5 _rep_i5 _value_i5 h_47 _Host_i4 _rep_i4 _value_i4 h_48 _Host_i6 _rep_i6 _value_i6 h_49 h_16 h_17 h_18 h_19
            let _object_w7 := (Litex.tuple (M := M) ![Litex.denote _value_i3, Litex.denote _value_i5] (Fin.cases (Litex.isSet _value_i3) (Fin.cases (Litex.isSet _value_i5) (fun i => Fin.elim0 i))))
            let _object_w8 := (Litex.tuple (M := M) ![Litex.denote _value_i4, Litex.denote _value_i6] (Fin.cases (Litex.isSet _value_i4) (Fin.cases (Litex.isSet _value_i6) (fun i => Fin.elim0 i))))
            have h_20 : (by
              let _equal_wd_1_0 := _object_w7
              let _equal_wd_1_1 := _object_w8
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (congrArg (Litex.FiniteFunction.tupleValue (M := M)) (funext (by
                      have _finiteProof_0 := (((h_16).trans (h_17).symm))
                      have _finiteProof_1 := (((h_18).trans (h_19).symm))
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )))
                  )
              )
            exact h_20
          )) _unique_left_i1 _member_left_i1 _unique_left_i2 _member_left_i2 _unique_right_i1 _member_right_i1 _unique_right_i2 _member_right_i2 _body_left_0 _body_right_0 _body_left_1 _body_right_1)⟩
      )
  )

theorem h_62 : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (_membership_i7 : M.mem (Litex.denote _value_i7) (M.standard Litex.StandardSetValue.real)) {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (_membership_i9 : M.mem (Litex.denote _value_i9) (M.standard Litex.StandardSetValue.real)) {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (_membership_i8 : M.mem (Litex.denote _value_i8) (M.standard Litex.StandardSetValue.real)) {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (_membership_i10 : M.mem (Litex.denote _value_i10) (M.standard Litex.StandardSetValue.real)) (h_55 : ((Litex.denote _value_i7) = (M.number (1 : ℂ)))) (h_56 : ((Litex.denote _value_i8) = (M.number (1 : ℂ)))) (h_57 : ((Litex.denote _value_i9) = (M.number (2 : ℂ)))) (h_58 : ((Litex.denote _value_i10) = (M.number (2 : ℂ)))), ((((Litex.denote _value_i7) = (Litex.denote _value_i8))) ∧ (((Litex.denote _value_i9) = (Litex.denote _value_i10)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 _membership_i7 _Host_i9 _rep_i9 _value_i9 _membership_i9 _Host_i8 _rep_i8 _value_i8 _membership_i8 _Host_i10 _rep_i10 _value_i10 _membership_i10 h_55 h_56 h_57 h_58
          have _unique : ∀ (_unique_left_i1 : Litex.Obj (M := M) M.Value) (_member_left_i1 : M.mem (Litex.denote _unique_left_i1) (M.standard Litex.StandardSetValue.real)) (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.mem (Litex.denote _unique_left_i2) (M.standard Litex.StandardSetValue.real)) (_unique_right_i1 : Litex.Obj (M := M) M.Value) (_member_right_i1 : M.mem (Litex.denote _unique_right_i1) (M.standard Litex.StandardSetValue.real)) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.mem (Litex.denote _unique_right_i2) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i1) = (M.number (1 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i1) = (M.number (1 : ℂ)))) (_body_left_1 : ((Litex.denote _unique_left_i2) = (M.number (2 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i2) = (M.number (2 : ℂ)))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i1), (Litex.denote _unique_left_i2)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i1), (Litex.denote _unique_right_i2)]) := ((h_3 (M := M))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i7) (Litex.isSet _value_i7)) _membership_i7 (Litex.semanticObject (Litex.denote _value_i9) (Litex.isSet _value_i9)) _membership_i9 (Litex.semanticObject (Litex.denote _value_i8) (Litex.isSet _value_i8)) _membership_i8 (Litex.semanticObject (Litex.denote _value_i10) (Litex.isSet _value_i10)) _membership_i10 h_55 h_56 h_57 h_58
          exact ⟨(by simpa only [Litex.FiniteFunction.call_tuple, Matrix.cons_val_zero, Matrix.cons_val_succ, Litex.semanticObject_denote] using congrArg (fun t => Litex.FunctionSemantics.callValue (M := M) t (Litex.FiniteFunction.index (0 : Fin 2))) _same), (by simpa only [Litex.FiniteFunction.call_tuple, Matrix.cons_val_zero, Matrix.cons_val_succ, Litex.semanticObject_denote] using congrArg (fun t => Litex.FunctionSemantics.callValue (M := M) t (Litex.FiniteFunction.index (Fin.succ (0 : Fin 1)))) _same)⟩)
      )
  )

theorem h_65 : (∃ (_value_i11 : Litex.Obj (M := M) M.Value), ∃ (h_66 : Litex.In _value_i11 (Litex.R (M := M))), ∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_67 : Litex.In _value_i12 (Litex.R (M := M))), ∃ (h_63 : Litex.Same _value_i11 (Litex.number (M := M) (1 : ℂ))), Litex.Same _value_i12 (Litex.number (M := M) (2 : ℂ))) ∧ (∀ (_unique_left_i11 : Litex.Obj (M := M) M.Value) (_member_left_i11 : M.mem (Litex.denote _unique_left_i11) (M.standard Litex.StandardSetValue.real)) (_unique_left_i12 : Litex.Obj (M := M) M.Value) (_member_left_i12 : M.mem (Litex.denote _unique_left_i12) (M.standard Litex.StandardSetValue.real)) (_unique_right_i11 : Litex.Obj (M := M) M.Value) (_member_right_i11 : M.mem (Litex.denote _unique_right_i11) (M.standard Litex.StandardSetValue.real)) (_unique_right_i12 : Litex.Obj (M := M) M.Value) (_member_right_i12 : M.mem (Litex.denote _unique_right_i12) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i11) = (M.number (1 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i11) = (M.number (1 : ℂ)))) (_body_left_1 : ((Litex.denote _unique_left_i12) = (M.number (2 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i12) = (M.number (2 : ℂ)))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i11), (Litex.denote _unique_left_i12)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i11), (Litex.denote _unique_right_i12)])) :=
  (by
    litex_complete =>
      exact (
        (h_3 (M := M))
      )
  )

theorem h_75 : ∀ {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (_membership_i13 : M.mem (Litex.denote _value_i13) (M.standard Litex.StandardSetValue.real)) {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (_membership_i15 : M.mem (Litex.denote _value_i15) (M.standard Litex.StandardSetValue.real)) {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (_membership_i14 : M.mem (Litex.denote _value_i14) (M.standard Litex.StandardSetValue.real)) {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (_membership_i16 : M.mem (Litex.denote _value_i16) (M.standard Litex.StandardSetValue.real)) (h_68 : ((Litex.denote _value_i13) = (M.number (1 : ℂ)))) (h_69 : ((Litex.denote _value_i14) = (M.number (1 : ℂ)))) (h_70 : ((Litex.denote _value_i15) = (M.number (2 : ℂ)))) (h_71 : ((Litex.denote _value_i16) = (M.number (2 : ℂ)))), ((((Litex.denote _value_i13) = (Litex.denote _value_i14))) ∧ (((Litex.denote _value_i15) = (Litex.denote _value_i16)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i13 _rep_i13 _value_i13 _membership_i13 _Host_i15 _rep_i15 _value_i15 _membership_i15 _Host_i14 _rep_i14 _value_i14 _membership_i14 _Host_i16 _rep_i16 _value_i16 _membership_i16 h_68 h_69 h_70 h_71
          have _unique : ∀ (_unique_left_i11 : Litex.Obj (M := M) M.Value) (_member_left_i11 : M.mem (Litex.denote _unique_left_i11) (M.standard Litex.StandardSetValue.real)) (_unique_left_i12 : Litex.Obj (M := M) M.Value) (_member_left_i12 : M.mem (Litex.denote _unique_left_i12) (M.standard Litex.StandardSetValue.real)) (_unique_right_i11 : Litex.Obj (M := M) M.Value) (_member_right_i11 : M.mem (Litex.denote _unique_right_i11) (M.standard Litex.StandardSetValue.real)) (_unique_right_i12 : Litex.Obj (M := M) M.Value) (_member_right_i12 : M.mem (Litex.denote _unique_right_i12) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i11) = (M.number (1 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i11) = (M.number (1 : ℂ)))) (_body_left_1 : ((Litex.denote _unique_left_i12) = (M.number (2 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i12) = (M.number (2 : ℂ)))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i11), (Litex.denote _unique_left_i12)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i11), (Litex.denote _unique_right_i12)]) := ((h_65 (M := M))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i13) (Litex.isSet _value_i13)) _membership_i13 (Litex.semanticObject (Litex.denote _value_i15) (Litex.isSet _value_i15)) _membership_i15 (Litex.semanticObject (Litex.denote _value_i14) (Litex.isSet _value_i14)) _membership_i14 (Litex.semanticObject (Litex.denote _value_i16) (Litex.isSet _value_i16)) _membership_i16 h_68 h_69 h_70 h_71
          exact ⟨(by simpa only [Litex.FiniteFunction.call_tuple, Matrix.cons_val_zero, Matrix.cons_val_succ, Litex.semanticObject_denote] using congrArg (fun t => Litex.FunctionSemantics.callValue (M := M) t (Litex.FiniteFunction.index (0 : Fin 2))) _same), (by simpa only [Litex.FiniteFunction.call_tuple, Matrix.cons_val_zero, Matrix.cons_val_succ, Litex.semanticObject_denote] using congrArg (fun t => Litex.FunctionSemantics.callValue (M := M) t (Litex.FiniteFunction.index (Fin.succ (0 : Fin 1)))) _same)⟩)
      )
  )

noncomputable def _value_i19 : Litex.Obj (M := M) M.Value :=
  Classical.choose (((show (∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_79 : Litex.In _value_i17 (Litex.R (M := M))), ∃ (_value_i18 : Litex.Obj (M := M) M.Value), ∃ (h_80 : Litex.In _value_i18 (Litex.R (M := M))), ∃ (h_76 : Litex.Same _value_i17 (Litex.number (M := M) (1 : ℂ))), Litex.Same _value_i18 (Litex.number (M := M) (2 : ℂ))) ∧ (∀ (_unique_left_i17 : Litex.Obj (M := M) M.Value) (_member_left_i17 : M.mem (Litex.denote _unique_left_i17) (M.standard Litex.StandardSetValue.real)) (_unique_left_i18 : Litex.Obj (M := M) M.Value) (_member_left_i18 : M.mem (Litex.denote _unique_left_i18) (M.standard Litex.StandardSetValue.real)) (_unique_right_i17 : Litex.Obj (M := M) M.Value) (_member_right_i17 : M.mem (Litex.denote _unique_right_i17) (M.standard Litex.StandardSetValue.real)) (_unique_right_i18 : Litex.Obj (M := M) M.Value) (_member_right_i18 : M.mem (Litex.denote _unique_right_i18) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i17) = (M.number (1 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i17) = (M.number (1 : ℂ)))) (_body_left_1 : ((Litex.denote _unique_left_i18) = (M.number (2 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i18) = (M.number (2 : ℂ)))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i17), (Litex.denote _unique_left_i18)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i17), (Litex.denote _unique_right_i18)])) from (h_3 (M := M)))).1)

theorem h_81 : Litex.In (_value_i19 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec (((show (∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_79 : Litex.In _value_i17 (Litex.R (M := M))), ∃ (_value_i18 : Litex.Obj (M := M) M.Value), ∃ (h_80 : Litex.In _value_i18 (Litex.R (M := M))), ∃ (h_76 : Litex.Same _value_i17 (Litex.number (M := M) (1 : ℂ))), Litex.Same _value_i18 (Litex.number (M := M) (2 : ℂ))) ∧ (∀ (_unique_left_i17 : Litex.Obj (M := M) M.Value) (_member_left_i17 : M.mem (Litex.denote _unique_left_i17) (M.standard Litex.StandardSetValue.real)) (_unique_left_i18 : Litex.Obj (M := M) M.Value) (_member_left_i18 : M.mem (Litex.denote _unique_left_i18) (M.standard Litex.StandardSetValue.real)) (_unique_right_i17 : Litex.Obj (M := M) M.Value) (_member_right_i17 : M.mem (Litex.denote _unique_right_i17) (M.standard Litex.StandardSetValue.real)) (_unique_right_i18 : Litex.Obj (M := M) M.Value) (_member_right_i18 : M.mem (Litex.denote _unique_right_i18) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i17) = (M.number (1 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i17) = (M.number (1 : ℂ)))) (_body_left_1 : ((Litex.denote _unique_left_i18) = (M.number (2 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i18) = (M.number (2 : ℂ)))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i17), (Litex.denote _unique_left_i18)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i17), (Litex.denote _unique_right_i18)])) from (h_3 (M := M)))).1))))
      )
  )

noncomputable def _value_i20 : Litex.Obj (M := M) M.Value :=
  Classical.choose ((Classical.choose_spec ((Classical.choose_spec (((show (∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_79 : Litex.In _value_i17 (Litex.R (M := M))), ∃ (_value_i18 : Litex.Obj (M := M) M.Value), ∃ (h_80 : Litex.In _value_i18 (Litex.R (M := M))), ∃ (h_76 : Litex.Same _value_i17 (Litex.number (M := M) (1 : ℂ))), Litex.Same _value_i18 (Litex.number (M := M) (2 : ℂ))) ∧ (∀ (_unique_left_i17 : Litex.Obj (M := M) M.Value) (_member_left_i17 : M.mem (Litex.denote _unique_left_i17) (M.standard Litex.StandardSetValue.real)) (_unique_left_i18 : Litex.Obj (M := M) M.Value) (_member_left_i18 : M.mem (Litex.denote _unique_left_i18) (M.standard Litex.StandardSetValue.real)) (_unique_right_i17 : Litex.Obj (M := M) M.Value) (_member_right_i17 : M.mem (Litex.denote _unique_right_i17) (M.standard Litex.StandardSetValue.real)) (_unique_right_i18 : Litex.Obj (M := M) M.Value) (_member_right_i18 : M.mem (Litex.denote _unique_right_i18) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i17) = (M.number (1 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i17) = (M.number (1 : ℂ)))) (_body_left_1 : ((Litex.denote _unique_left_i18) = (M.number (2 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i18) = (M.number (2 : ℂ)))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i17), (Litex.denote _unique_left_i18)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i17), (Litex.denote _unique_right_i18)])) from (h_3 (M := M)))).1)))))

theorem h_82 : Litex.In (_value_i20 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec (((show (∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_79 : Litex.In _value_i17 (Litex.R (M := M))), ∃ (_value_i18 : Litex.Obj (M := M) M.Value), ∃ (h_80 : Litex.In _value_i18 (Litex.R (M := M))), ∃ (h_76 : Litex.Same _value_i17 (Litex.number (M := M) (1 : ℂ))), Litex.Same _value_i18 (Litex.number (M := M) (2 : ℂ))) ∧ (∀ (_unique_left_i17 : Litex.Obj (M := M) M.Value) (_member_left_i17 : M.mem (Litex.denote _unique_left_i17) (M.standard Litex.StandardSetValue.real)) (_unique_left_i18 : Litex.Obj (M := M) M.Value) (_member_left_i18 : M.mem (Litex.denote _unique_left_i18) (M.standard Litex.StandardSetValue.real)) (_unique_right_i17 : Litex.Obj (M := M) M.Value) (_member_right_i17 : M.mem (Litex.denote _unique_right_i17) (M.standard Litex.StandardSetValue.real)) (_unique_right_i18 : Litex.Obj (M := M) M.Value) (_member_right_i18 : M.mem (Litex.denote _unique_right_i18) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i17) = (M.number (1 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i17) = (M.number (1 : ℂ)))) (_body_left_1 : ((Litex.denote _unique_left_i18) = (M.number (2 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i18) = (M.number (2 : ℂ)))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i17), (Litex.denote _unique_left_i18)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i17), (Litex.denote _unique_right_i18)])) from (h_3 (M := M)))).1))))))))
      )
  )

theorem h_83 : Litex.Same (_value_i19 (M := M)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec (((show (∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_79 : Litex.In _value_i17 (Litex.R (M := M))), ∃ (_value_i18 : Litex.Obj (M := M) M.Value), ∃ (h_80 : Litex.In _value_i18 (Litex.R (M := M))), ∃ (h_76 : Litex.Same _value_i17 (Litex.number (M := M) (1 : ℂ))), Litex.Same _value_i18 (Litex.number (M := M) (2 : ℂ))) ∧ (∀ (_unique_left_i17 : Litex.Obj (M := M) M.Value) (_member_left_i17 : M.mem (Litex.denote _unique_left_i17) (M.standard Litex.StandardSetValue.real)) (_unique_left_i18 : Litex.Obj (M := M) M.Value) (_member_left_i18 : M.mem (Litex.denote _unique_left_i18) (M.standard Litex.StandardSetValue.real)) (_unique_right_i17 : Litex.Obj (M := M) M.Value) (_member_right_i17 : M.mem (Litex.denote _unique_right_i17) (M.standard Litex.StandardSetValue.real)) (_unique_right_i18 : Litex.Obj (M := M) M.Value) (_member_right_i18 : M.mem (Litex.denote _unique_right_i18) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i17) = (M.number (1 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i17) = (M.number (1 : ℂ)))) (_body_left_1 : ((Litex.denote _unique_left_i18) = (M.number (2 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i18) = (M.number (2 : ℂ)))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i17), (Litex.denote _unique_left_i18)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i17), (Litex.denote _unique_right_i18)])) from (h_3 (M := M)))).1))))))))))
      )
  )

theorem h_84 : Litex.Same (_value_i20 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec ((Classical.choose_spec (((show (∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_79 : Litex.In _value_i17 (Litex.R (M := M))), ∃ (_value_i18 : Litex.Obj (M := M) M.Value), ∃ (h_80 : Litex.In _value_i18 (Litex.R (M := M))), ∃ (h_76 : Litex.Same _value_i17 (Litex.number (M := M) (1 : ℂ))), Litex.Same _value_i18 (Litex.number (M := M) (2 : ℂ))) ∧ (∀ (_unique_left_i17 : Litex.Obj (M := M) M.Value) (_member_left_i17 : M.mem (Litex.denote _unique_left_i17) (M.standard Litex.StandardSetValue.real)) (_unique_left_i18 : Litex.Obj (M := M) M.Value) (_member_left_i18 : M.mem (Litex.denote _unique_left_i18) (M.standard Litex.StandardSetValue.real)) (_unique_right_i17 : Litex.Obj (M := M) M.Value) (_member_right_i17 : M.mem (Litex.denote _unique_right_i17) (M.standard Litex.StandardSetValue.real)) (_unique_right_i18 : Litex.Obj (M := M) M.Value) (_member_right_i18 : M.mem (Litex.denote _unique_right_i18) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i17) = (M.number (1 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i17) = (M.number (1 : ℂ)))) (_body_left_1 : ((Litex.denote _unique_left_i18) = (M.number (2 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i18) = (M.number (2 : ℂ)))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i17), (Litex.denote _unique_left_i18)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i17), (Litex.denote _unique_right_i18)])) from (h_3 (M := M)))).1))))))))))
      )
  )

theorem h_90 : ∀ {_Host_i21 : Type _} [_rep_i21 : Litex.Representation M _Host_i21] (_value_i21 : Litex.Obj (M := M) _Host_i21) (_membership_i21 : M.mem (Litex.denote _value_i21) (M.standard Litex.StandardSetValue.real)) {_Host_i23 : Type _} [_rep_i23 : Litex.Representation M _Host_i23] (_value_i23 : Litex.Obj (M := M) _Host_i23) (_membership_i23 : M.mem (Litex.denote _value_i23) (M.standard Litex.StandardSetValue.real)) {_Host_i22 : Type _} [_rep_i22 : Litex.Representation M _Host_i22] (_value_i22 : Litex.Obj (M := M) _Host_i22) (_membership_i22 : M.mem (Litex.denote _value_i22) (M.standard Litex.StandardSetValue.real)) {_Host_i24 : Type _} [_rep_i24 : Litex.Representation M _Host_i24] (_value_i24 : Litex.Obj (M := M) _Host_i24) (_membership_i24 : M.mem (Litex.denote _value_i24) (M.standard Litex.StandardSetValue.real)) (h_85 : ((Litex.denote _value_i21) = (M.number (1 : ℂ)))) (h_86 : ((Litex.denote _value_i22) = (M.number (1 : ℂ)))) (h_87 : ((Litex.denote _value_i23) = (M.number (2 : ℂ)))) (h_88 : ((Litex.denote _value_i24) = (M.number (2 : ℂ)))), ((Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i21), (Litex.denote _value_i23)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i22), (Litex.denote _value_i24)])) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i21 _rep_i21 _value_i21 _membership_i21 _Host_i23 _rep_i23 _value_i23 _membership_i23 _Host_i22 _rep_i22 _value_i22 _membership_i22 _Host_i24 _rep_i24 _value_i24 _membership_i24 h_85 h_86 h_87 h_88
          have _unique : ∀ (_unique_left_i17 : Litex.Obj (M := M) M.Value) (_member_left_i17 : M.mem (Litex.denote _unique_left_i17) (M.standard Litex.StandardSetValue.real)) (_unique_left_i18 : Litex.Obj (M := M) M.Value) (_member_left_i18 : M.mem (Litex.denote _unique_left_i18) (M.standard Litex.StandardSetValue.real)) (_unique_right_i17 : Litex.Obj (M := M) M.Value) (_member_right_i17 : M.mem (Litex.denote _unique_right_i17) (M.standard Litex.StandardSetValue.real)) (_unique_right_i18 : Litex.Obj (M := M) M.Value) (_member_right_i18 : M.mem (Litex.denote _unique_right_i18) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i17) = (M.number (1 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i17) = (M.number (1 : ℂ)))) (_body_left_1 : ((Litex.denote _unique_left_i18) = (M.number (2 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i18) = (M.number (2 : ℂ)))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i17), (Litex.denote _unique_left_i18)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i17), (Litex.denote _unique_right_i18)]) := ((show (∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_79 : Litex.In _value_i17 (Litex.R (M := M))), ∃ (_value_i18 : Litex.Obj (M := M) M.Value), ∃ (h_80 : Litex.In _value_i18 (Litex.R (M := M))), ∃ (h_76 : Litex.Same _value_i17 (Litex.number (M := M) (1 : ℂ))), Litex.Same _value_i18 (Litex.number (M := M) (2 : ℂ))) ∧ (∀ (_unique_left_i17 : Litex.Obj (M := M) M.Value) (_member_left_i17 : M.mem (Litex.denote _unique_left_i17) (M.standard Litex.StandardSetValue.real)) (_unique_left_i18 : Litex.Obj (M := M) M.Value) (_member_left_i18 : M.mem (Litex.denote _unique_left_i18) (M.standard Litex.StandardSetValue.real)) (_unique_right_i17 : Litex.Obj (M := M) M.Value) (_member_right_i17 : M.mem (Litex.denote _unique_right_i17) (M.standard Litex.StandardSetValue.real)) (_unique_right_i18 : Litex.Obj (M := M) M.Value) (_member_right_i18 : M.mem (Litex.denote _unique_right_i18) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i17) = (M.number (1 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i17) = (M.number (1 : ℂ)))) (_body_left_1 : ((Litex.denote _unique_left_i18) = (M.number (2 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i18) = (M.number (2 : ℂ)))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i17), (Litex.denote _unique_left_i18)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i17), (Litex.denote _unique_right_i18)])) from (h_3 (M := M)))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i21) (Litex.isSet _value_i21)) _membership_i21 (Litex.semanticObject (Litex.denote _value_i23) (Litex.isSet _value_i23)) _membership_i23 (Litex.semanticObject (Litex.denote _value_i22) (Litex.isSet _value_i22)) _membership_i22 (Litex.semanticObject (Litex.denote _value_i24) (Litex.isSet _value_i24)) _membership_i24 h_85 h_86 h_87 h_88
          exact _same)
      )
  )

theorem h_91 : Litex.Same (_value_i19 (M := M)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (h_83 (M := M))
      )
  )

theorem h_93 : Litex.Same (_value_i20 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (h_84 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_real_x5f_pair_x2f_statement_x2e_lit
