import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_pair_x5f_contradiction_x5f_closing_x2f_statement_x2e_lit

universe u v11 v12 v13 v14
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_4 : Litex.In _value_i1 (Litex.R (M := M))), ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_5 : Litex.In _value_i2 (Litex.R (M := M))), ∃ (h_1 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))), Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ))) ∧ (∀ (_unique_left_i1 : Litex.Obj (M := M) M.Value) (_member_left_i1 : M.mem (Litex.denote _unique_left_i1) (M.standard Litex.StandardSetValue.real)) (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.mem (Litex.denote _unique_left_i2) (M.standard Litex.StandardSetValue.real)) (_unique_right_i1 : Litex.Obj (M := M) M.Value) (_member_right_i1 : M.mem (Litex.denote _unique_right_i1) (M.standard Litex.StandardSetValue.real)) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.mem (Litex.denote _unique_right_i2) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i1) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i1) = (M.number (0 : ℂ)))) (_body_left_1 : ((Litex.denote _unique_left_i2) = (M.number (1 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i2) = (M.number (1 : ℂ)))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i1), (Litex.denote _unique_left_i2)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i1), (Litex.denote _unique_right_i2)])) :=
  (by
    litex_complete =>
      exact (
        by
          let _value_i1 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.isSet (Litex.number (M := M) (0 : ℂ)))
          have h_8 : Litex.In _value_i1 (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
          let _value_i2 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (1 : ℂ))) (Litex.isSet (Litex.number (M := M) (1 : ℂ)))
          have h_9 : Litex.In _value_i2 (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
          have h_10 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) := rfl
          have h_11 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)) := rfl
          have h_12 : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
          have h_14 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
          exact ⟨⟨_value_i1, h_8, _value_i2, h_9, h_12, h_14⟩, (by
            intro _unique_left_i1 _member_left_i1 _unique_left_i2 _member_left_i2 _unique_right_i1 _member_right_i1 _unique_right_i2 _member_right_i2 _body_left_0 _body_right_0 _body_left_1 _body_right_1
            exact (show ∀ {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_70 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_71 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_72 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_73 : Litex.In _value_i6 (Litex.R (M := M))) (h_16 : Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))) (h_17 : Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))) (h_18 : Litex.Same _value_i5 (Litex.number (M := M) (1 : ℂ))) (h_19 : Litex.Same _value_i6 (Litex.number (M := M) (1 : ℂ))), (by
            let _object_w7 := (Litex.tuple (M := M) ![Litex.denote _value_i3, Litex.denote _value_i5] (Fin.cases (Litex.isSet _value_i3) (Fin.cases (Litex.isSet _value_i5) (fun i => Fin.elim0 i))))
            let _object_w8 := (Litex.tuple (M := M) ![Litex.denote _value_i4, Litex.denote _value_i6] (Fin.cases (Litex.isSet _value_i4) (Fin.cases (Litex.isSet _value_i6) (fun i => Fin.elim0 i))))
            exact (by
              let _equal_wd_1_0 := _object_w7
              let _equal_wd_1_1 := _object_w8
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
          ) from (by
            intro _Host_i3 _rep_i3 _value_i3 h_70 _Host_i5 _rep_i5 _value_i5 h_71 _Host_i4 _rep_i4 _value_i4 h_72 _Host_i6 _rep_i6 _value_i6 h_73 h_16 h_17 h_18 h_19
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

theorem h_86 : ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (_membership_i7 : M.mem (Litex.denote _value_i7) (M.standard Litex.StandardSetValue.real)) {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (_membership_i9 : M.mem (Litex.denote _value_i9) (M.standard Litex.StandardSetValue.real)) {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (_membership_i8 : M.mem (Litex.denote _value_i8) (M.standard Litex.StandardSetValue.real)) {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (_membership_i10 : M.mem (Litex.denote _value_i10) (M.standard Litex.StandardSetValue.real)) (h_79 : ((Litex.denote _value_i7) = (M.number (0 : ℂ)))) (h_80 : ((Litex.denote _value_i8) = (M.number (0 : ℂ)))) (h_81 : ((Litex.denote _value_i9) = (M.number (1 : ℂ)))) (h_82 : ((Litex.denote _value_i10) = (M.number (1 : ℂ)))), ((((Litex.denote _value_i7) = (Litex.denote _value_i8))) ∧ (((Litex.denote _value_i9) = (Litex.denote _value_i10)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 _membership_i7 _Host_i9 _rep_i9 _value_i9 _membership_i9 _Host_i8 _rep_i8 _value_i8 _membership_i8 _Host_i10 _rep_i10 _value_i10 _membership_i10 h_79 h_80 h_81 h_82
          have _unique : ∀ (_unique_left_i1 : Litex.Obj (M := M) M.Value) (_member_left_i1 : M.mem (Litex.denote _unique_left_i1) (M.standard Litex.StandardSetValue.real)) (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.mem (Litex.denote _unique_left_i2) (M.standard Litex.StandardSetValue.real)) (_unique_right_i1 : Litex.Obj (M := M) M.Value) (_member_right_i1 : M.mem (Litex.denote _unique_right_i1) (M.standard Litex.StandardSetValue.real)) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.mem (Litex.denote _unique_right_i2) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i1) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i1) = (M.number (0 : ℂ)))) (_body_left_1 : ((Litex.denote _unique_left_i2) = (M.number (1 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i2) = (M.number (1 : ℂ)))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i1), (Litex.denote _unique_left_i2)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i1), (Litex.denote _unique_right_i2)]) := ((h_3 (M := M))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i7) (Litex.isSet _value_i7)) _membership_i7 (Litex.semanticObject (Litex.denote _value_i9) (Litex.isSet _value_i9)) _membership_i9 (Litex.semanticObject (Litex.denote _value_i8) (Litex.isSet _value_i8)) _membership_i8 (Litex.semanticObject (Litex.denote _value_i10) (Litex.isSet _value_i10)) _membership_i10 h_79 h_80 h_81 h_82
          exact ⟨(by simpa only [Litex.FiniteFunction.call_tuple, Matrix.cons_val_zero, Matrix.cons_val_succ, Litex.semanticObject_denote] using congrArg (fun t => Litex.FunctionSemantics.callValue (M := M) t (Litex.FiniteFunction.index (0 : Fin 2))) _same), (by simpa only [Litex.FiniteFunction.call_tuple, Matrix.cons_val_zero, Matrix.cons_val_succ, Litex.semanticObject_denote] using congrArg (fun t => Litex.FunctionSemantics.callValue (M := M) t (Litex.FiniteFunction.index (Fin.succ (0 : Fin 1)))) _same)⟩)
      )
  )

theorem h_89 : (∃ (_value_i11 : Litex.Obj (M := M) M.Value), ∃ (h_93 : Litex.In _value_i11 (Litex.R (M := M))), ∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_94 : Litex.In _value_i12 (Litex.R (M := M))), ∃ (h_87 : Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ))), Litex.Same _value_i12 (Litex.number (M := M) (1 : ℂ))) ∧ (∀ (_unique_left_i11 : Litex.Obj (M := M) M.Value) (_member_left_i11 : M.mem (Litex.denote _unique_left_i11) (M.standard Litex.StandardSetValue.real)) (_unique_left_i12 : Litex.Obj (M := M) M.Value) (_member_left_i12 : M.mem (Litex.denote _unique_left_i12) (M.standard Litex.StandardSetValue.real)) (_unique_right_i11 : Litex.Obj (M := M) M.Value) (_member_right_i11 : M.mem (Litex.denote _unique_right_i11) (M.standard Litex.StandardSetValue.real)) (_unique_right_i12 : Litex.Obj (M := M) M.Value) (_member_right_i12 : M.mem (Litex.denote _unique_right_i12) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i11) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i11) = (M.number (0 : ℂ)))) (_body_left_1 : ((Litex.denote _unique_left_i12) = (M.number (1 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i12) = (M.number (1 : ℂ)))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i11), (Litex.denote _unique_left_i12)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i11), (Litex.denote _unique_right_i12)])) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          apply Classical.byContradiction
          intro _litex_negated_goal
          have h_101 : ∀ (_value_i11 : Litex.Obj (M := M) M.Value) (h_102 : Litex.In _value_i11 (Litex.R (M := M))) (_value_i12 : Litex.Obj (M := M) M.Value) (h_103 : Litex.In _value_i12 (Litex.R (M := M))) (h_87 : Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ))) (h_88 : Litex.Same _value_i12 (Litex.number (M := M) (1 : ℂ))), ∃ (_value_i15 : Litex.Obj (M := M) M.Value), ∃ (h_104 : Litex.In _value_i15 (Litex.R (M := M))), ∃ (_value_i16 : Litex.Obj (M := M) M.Value), ∃ (h_105 : Litex.In _value_i16 (Litex.R (M := M))), ∃ (h_97 : Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ))), ∃ (h_98 : Litex.Same _value_i16 (Litex.number (M := M) (1 : ℂ))), ((¬ Litex.Same _value_i15 _value_i11) ∨ (¬ Litex.Same _value_i16 _value_i12)) := (by
            classical
            intro _value_i11 h_102 _value_i12 h_103 h_87 h_88
            apply Classical.byContradiction
            intro _no_alternative
            apply _litex_negated_goal
            constructor
            · exact ⟨(Litex.semanticObject (Litex.denote _value_i11) (Litex.isSet _value_i11)), h_102, (Litex.semanticObject (Litex.denote _value_i12) (Litex.isSet _value_i12)), h_103, h_87, h_88⟩
            · intro _unique_left_i11 _member_left_i11 _unique_left_i12 _member_left_i12 _unique_right_i11 _member_right_i11 _unique_right_i12 _member_right_i12 _body_left_0 _body_right_0 _body_left_1 _body_right_1
              have _same_left_i11 : Litex.denote _unique_left_i11 = Litex.denote _value_i11 := by
                apply Classical.byContradiction
                intro _different
                apply _no_alternative
                exact ⟨_unique_left_i11, _member_left_i11, _unique_left_i12, _member_left_i12, _body_left_0, _body_left_1, (Or.inl _different)⟩
              have _same_left_i12 : Litex.denote _unique_left_i12 = Litex.denote _value_i12 := by
                apply Classical.byContradiction
                intro _different
                apply _no_alternative
                exact ⟨_unique_left_i11, _member_left_i11, _unique_left_i12, _member_left_i12, _body_left_0, _body_left_1, (Or.inr _different)⟩
              have _same_right_i11 : Litex.denote _unique_right_i11 = Litex.denote _value_i11 := by
                apply Classical.byContradiction
                intro _different
                apply _no_alternative
                exact ⟨_unique_right_i11, _member_right_i11, _unique_right_i12, _member_right_i12, _body_right_0, _body_right_1, (Or.inl _different)⟩
              have _same_right_i12 : Litex.denote _unique_right_i12 = Litex.denote _value_i12 := by
                apply Classical.byContradiction
                intro _different
                apply _no_alternative
                exact ⟨_unique_right_i11, _member_right_i11, _unique_right_i12, _member_right_i12, _body_right_0, _body_right_1, (Or.inr _different)⟩
              simp only [_same_left_i11, _same_left_i12, _same_right_i11, _same_right_i12])
          exact (by
            have _unique_exists : (∃ (_value_i13 : Litex.Obj (M := M) M.Value), ∃ (h_106 : Litex.In _value_i13 (Litex.R (M := M))), ∃ (_value_i14 : Litex.Obj (M := M) M.Value), ∃ (h_107 : Litex.In _value_i14 (Litex.R (M := M))), ∃ (h_90 : Litex.Same _value_i13 (Litex.number (M := M) (0 : ℂ))), Litex.Same _value_i14 (Litex.number (M := M) (1 : ℂ))) ∧ (∀ (_unique_left_i13 : Litex.Obj (M := M) M.Value) (_member_left_i13 : M.mem (Litex.denote _unique_left_i13) (M.standard Litex.StandardSetValue.real)) (_unique_left_i14 : Litex.Obj (M := M) M.Value) (_member_left_i14 : M.mem (Litex.denote _unique_left_i14) (M.standard Litex.StandardSetValue.real)) (_unique_right_i13 : Litex.Obj (M := M) M.Value) (_member_right_i13 : M.mem (Litex.denote _unique_right_i13) (M.standard Litex.StandardSetValue.real)) (_unique_right_i14 : Litex.Obj (M := M) M.Value) (_member_right_i14 : M.mem (Litex.denote _unique_right_i14) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i13) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i13) = (M.number (0 : ℂ)))) (_body_left_1 : ((Litex.denote _unique_left_i14) = (M.number (1 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i14) = (M.number (1 : ℂ)))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i13), (Litex.denote _unique_left_i14)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i13), (Litex.denote _unique_right_i14)])) := (h_3 (M := M))
            have _alternative : ∀ {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_123 : Litex.In _value_i13 (Litex.R (M := M))) {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_124 : Litex.In _value_i14 (Litex.R (M := M))) (h_90 : Litex.Same _value_i13 (Litex.number (M := M) (0 : ℂ))) (h_91 : Litex.Same _value_i14 (Litex.number (M := M) (1 : ℂ))), ∃ (_value_i17 : Litex.Obj (M := M) M.Value), ∃ (h_125 : Litex.In _value_i17 (Litex.R (M := M))), ∃ (_value_i18 : Litex.Obj (M := M) M.Value), ∃ (h_126 : Litex.In _value_i18 (Litex.R (M := M))), ∃ (h_110 : Litex.Same _value_i17 (Litex.number (M := M) (0 : ℂ))), ∃ (h_111 : Litex.Same _value_i18 (Litex.number (M := M) (1 : ℂ))), ((¬ Litex.Same _value_i17 _value_i13) ∨ (¬ Litex.Same _value_i18 _value_i14)) := (by
              intro _Host_i13 _rep_i13 _value_i13 h_123 _Host_i14 _rep_i14 _value_i14 h_124 h_90 h_91
              exact ((show ∀ {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_102 : Litex.In _value_i11 (Litex.R (M := M))) {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_103 : Litex.In _value_i12 (Litex.R (M := M))) (h_87 : Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ))) (h_88 : Litex.Same _value_i12 (Litex.number (M := M) (1 : ℂ))), ∃ (_value_i15 : Litex.Obj (M := M) M.Value), ∃ (h_104 : Litex.In _value_i15 (Litex.R (M := M))), ∃ (_value_i16 : Litex.Obj (M := M) M.Value), ∃ (h_105 : Litex.In _value_i16 (Litex.R (M := M))), ∃ (h_97 : Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ))), ∃ (h_98 : Litex.Same _value_i16 (Litex.number (M := M) (1 : ℂ))), ((¬ Litex.Same _value_i15 _value_i11) ∨ (¬ Litex.Same _value_i16 _value_i12)) from (fun {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_102 : Litex.In _value_i11 (Litex.R (M := M))) {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_103 : Litex.In _value_i12 (Litex.R (M := M))) (h_87 : Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ))) (h_88 : Litex.Same _value_i12 (Litex.number (M := M) (1 : ℂ))) => by
              exact h_101 (Litex.semanticObject (Litex.denote _value_i11) (Litex.isSet _value_i11)) h_102 (Litex.semanticObject (Litex.denote _value_i12) (Litex.isSet _value_i12)) h_103 h_87 h_88)) _value_i13 h_123 _value_i14 h_124 h_90 h_91)
            )
            rcases _unique_exists with ⟨_exists, _unique⟩
            rcases _exists with ⟨_unique_left_i13, _member_left_i13, _unique_left_i14, _member_left_i14, _body_left_0, _body_left_1⟩
            obtain ⟨_unique_right_i13, _member_right_i13, _unique_right_i14, _member_right_i14, _body_right_0, _body_right_1, _different⟩ := _alternative _unique_left_i13 _member_left_i13 _unique_left_i14 _member_left_i14 _body_left_0 _body_left_1
            have _same := _unique _unique_left_i13 _member_left_i13 _unique_left_i14 _member_left_i14 _unique_right_i13 _member_right_i13 _unique_right_i14 _member_right_i14 _body_left_0 _body_right_0 _body_left_1 _body_right_1
            rcases _different with _different | _different
            · apply _different
              simpa only [Litex.Same, Litex.FiniteFunction.call_tuple, Matrix.cons_val_zero, Matrix.cons_val_succ, Litex.semanticObject_denote] using (congrArg (fun t => Litex.FunctionSemantics.callValue (M := M) t (Litex.FiniteFunction.index (0 : Fin 2))) _same).symm
            · apply _different
              simpa only [Litex.Same, Litex.FiniteFunction.call_tuple, Matrix.cons_val_zero, Matrix.cons_val_succ, Litex.semanticObject_denote] using (congrArg (fun t => Litex.FunctionSemantics.callValue (M := M) t (Litex.FiniteFunction.index (Fin.succ (0 : Fin 1)))) _same).symm)
        )
      )
  )

theorem h_136 : ∀ {_Host_i19 : Type _} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (_membership_i19 : M.mem (Litex.denote _value_i19) (M.standard Litex.StandardSetValue.real)) {_Host_i21 : Type _} [_rep_i21 : Litex.Representation M _Host_i21] (_value_i21 : Litex.Obj (M := M) _Host_i21) (_membership_i21 : M.mem (Litex.denote _value_i21) (M.standard Litex.StandardSetValue.real)) {_Host_i20 : Type _} [_rep_i20 : Litex.Representation M _Host_i20] (_value_i20 : Litex.Obj (M := M) _Host_i20) (_membership_i20 : M.mem (Litex.denote _value_i20) (M.standard Litex.StandardSetValue.real)) {_Host_i22 : Type _} [_rep_i22 : Litex.Representation M _Host_i22] (_value_i22 : Litex.Obj (M := M) _Host_i22) (_membership_i22 : M.mem (Litex.denote _value_i22) (M.standard Litex.StandardSetValue.real)) (h_129 : ((Litex.denote _value_i19) = (M.number (0 : ℂ)))) (h_130 : ((Litex.denote _value_i20) = (M.number (0 : ℂ)))) (h_131 : ((Litex.denote _value_i21) = (M.number (1 : ℂ)))) (h_132 : ((Litex.denote _value_i22) = (M.number (1 : ℂ)))), ((((Litex.denote _value_i19) = (Litex.denote _value_i20))) ∧ (((Litex.denote _value_i21) = (Litex.denote _value_i22)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i19 _rep_i19 _value_i19 _membership_i19 _Host_i21 _rep_i21 _value_i21 _membership_i21 _Host_i20 _rep_i20 _value_i20 _membership_i20 _Host_i22 _rep_i22 _value_i22 _membership_i22 h_129 h_130 h_131 h_132
          have _unique : ∀ (_unique_left_i11 : Litex.Obj (M := M) M.Value) (_member_left_i11 : M.mem (Litex.denote _unique_left_i11) (M.standard Litex.StandardSetValue.real)) (_unique_left_i12 : Litex.Obj (M := M) M.Value) (_member_left_i12 : M.mem (Litex.denote _unique_left_i12) (M.standard Litex.StandardSetValue.real)) (_unique_right_i11 : Litex.Obj (M := M) M.Value) (_member_right_i11 : M.mem (Litex.denote _unique_right_i11) (M.standard Litex.StandardSetValue.real)) (_unique_right_i12 : Litex.Obj (M := M) M.Value) (_member_right_i12 : M.mem (Litex.denote _unique_right_i12) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i11) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i11) = (M.number (0 : ℂ)))) (_body_left_1 : ((Litex.denote _unique_left_i12) = (M.number (1 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i12) = (M.number (1 : ℂ)))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i11), (Litex.denote _unique_left_i12)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i11), (Litex.denote _unique_right_i12)]) := ((h_89 (M := M))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i19) (Litex.isSet _value_i19)) _membership_i19 (Litex.semanticObject (Litex.denote _value_i21) (Litex.isSet _value_i21)) _membership_i21 (Litex.semanticObject (Litex.denote _value_i20) (Litex.isSet _value_i20)) _membership_i20 (Litex.semanticObject (Litex.denote _value_i22) (Litex.isSet _value_i22)) _membership_i22 h_129 h_130 h_131 h_132
          exact ⟨(by simpa only [Litex.FiniteFunction.call_tuple, Matrix.cons_val_zero, Matrix.cons_val_succ, Litex.semanticObject_denote] using congrArg (fun t => Litex.FunctionSemantics.callValue (M := M) t (Litex.FiniteFunction.index (0 : Fin 2))) _same), (by simpa only [Litex.FiniteFunction.call_tuple, Matrix.cons_val_zero, Matrix.cons_val_succ, Litex.semanticObject_denote] using congrArg (fun t => Litex.FunctionSemantics.callValue (M := M) t (Litex.FiniteFunction.index (Fin.succ (0 : Fin 1)))) _same)⟩)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_pair_x5f_contradiction_x5f_closing_x2f_statement_x2e_lit
