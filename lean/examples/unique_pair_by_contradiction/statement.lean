import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_pair_x5f_by_x5f_contradiction_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_13 : Litex.In _value_i1 (Litex.R (M := M))), ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_14 : Litex.In _value_i2 (Litex.R (M := M))), ∃ (h_1 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))), Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ))) ∧ (∀ (_unique_left_i1 : Litex.Obj (M := M) M.Value) (_member_left_i1 : M.mem (Litex.denote _unique_left_i1) (M.standard Litex.StandardSetValue.real)) (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.mem (Litex.denote _unique_left_i2) (M.standard Litex.StandardSetValue.real)) (_unique_right_i1 : Litex.Obj (M := M) M.Value) (_member_right_i1 : M.mem (Litex.denote _unique_right_i1) (M.standard Litex.StandardSetValue.real)) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.mem (Litex.denote _unique_right_i2) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i1) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i1) = (M.number (0 : ℂ)))) (_body_left_1 : ((Litex.denote _unique_left_i2) = (M.number (1 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i2) = (M.number (1 : ℂ)))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i1), (Litex.denote _unique_left_i2)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i1), (Litex.denote _unique_right_i2)])) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          apply Classical.byContradiction
          intro _litex_negated_goal
          have h_21 : ∀ (_value_i1 : Litex.Obj (M := M) M.Value) (h_22 : Litex.In _value_i1 (Litex.R (M := M))) (_value_i2 : Litex.Obj (M := M) M.Value) (h_23 : Litex.In _value_i2 (Litex.R (M := M))) (h_1 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))) (h_2 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ))), ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_24 : Litex.In _value_i7 (Litex.R (M := M))), ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_25 : Litex.In _value_i8 (Litex.R (M := M))), ∃ (h_17 : Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ))), ∃ (h_18 : Litex.Same _value_i8 (Litex.number (M := M) (1 : ℂ))), ((¬ Litex.Same _value_i7 _value_i1) ∨ (¬ Litex.Same _value_i8 _value_i2)) := (by
            classical
            intro _value_i1 h_22 _value_i2 h_23 h_1 h_2
            apply Classical.byContradiction
            intro _no_alternative
            apply _litex_negated_goal
            constructor
            · exact ⟨(Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1)), h_22, (Litex.semanticObject (Litex.denote _value_i2) (Litex.isSet _value_i2)), h_23, h_1, h_2⟩
            · intro _unique_left_i1 _member_left_i1 _unique_left_i2 _member_left_i2 _unique_right_i1 _member_right_i1 _unique_right_i2 _member_right_i2 _body_left_0 _body_right_0 _body_left_1 _body_right_1
              have _same_left_i1 : Litex.denote _unique_left_i1 = Litex.denote _value_i1 := by
                apply Classical.byContradiction
                intro _different
                apply _no_alternative
                exact ⟨_unique_left_i1, _member_left_i1, _unique_left_i2, _member_left_i2, _body_left_0, _body_left_1, (Or.inl _different)⟩
              have _same_left_i2 : Litex.denote _unique_left_i2 = Litex.denote _value_i2 := by
                apply Classical.byContradiction
                intro _different
                apply _no_alternative
                exact ⟨_unique_left_i1, _member_left_i1, _unique_left_i2, _member_left_i2, _body_left_0, _body_left_1, (Or.inr _different)⟩
              have _same_right_i1 : Litex.denote _unique_right_i1 = Litex.denote _value_i1 := by
                apply Classical.byContradiction
                intro _different
                apply _no_alternative
                exact ⟨_unique_right_i1, _member_right_i1, _unique_right_i2, _member_right_i2, _body_right_0, _body_right_1, (Or.inl _different)⟩
              have _same_right_i2 : Litex.denote _unique_right_i2 = Litex.denote _value_i2 := by
                apply Classical.byContradiction
                intro _different
                apply _no_alternative
                exact ⟨_unique_right_i1, _member_right_i1, _unique_right_i2, _member_right_i2, _body_right_0, _body_right_1, (Or.inr _different)⟩
              simp only [_same_left_i1, _same_left_i2, _same_right_i1, _same_right_i2])
          rcases (show ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_26 : Litex.In _value_i3 (Litex.R (M := M))), ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_27 : Litex.In _value_i4 (Litex.R (M := M))), ∃ (h_4 : Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))), ∃ (h_5 : Litex.Same _value_i4 (Litex.number (M := M) (1 : ℂ))), ((¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))) ∨ (¬ Litex.Same _value_i4 (Litex.number (M := M) (1 : ℂ)))) from (by
            have h_47 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) :=
              (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
            have h_48 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
              (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
            have h_49 : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
              (show @Eq M.Value _ _ from Eq.refl _)
            have h_50 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
              (show @Eq M.Value _ _ from Eq.refl _)
            rcases ((show ∀ {_Host_i1 : Type _} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_22 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type _} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_23 : Litex.In _value_i2 (Litex.R (M := M))) (h_1 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))) (h_2 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ))), ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_24 : Litex.In _value_i7 (Litex.R (M := M))), ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_25 : Litex.In _value_i8 (Litex.R (M := M))), ∃ (h_17 : Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ))), ∃ (h_18 : Litex.Same _value_i8 (Litex.number (M := M) (1 : ℂ))), ((¬ Litex.Same _value_i7 _value_i1) ∨ (¬ Litex.Same _value_i8 _value_i2)) from (fun {_Host_i1 : Type _} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_22 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type _} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_23 : Litex.In _value_i2 (Litex.R (M := M))) (h_1 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))) (h_2 : Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ))) => by
              exact h_21 (Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1)) h_22 (Litex.semanticObject (Litex.denote _value_i2) (Litex.isSet _value_i2)) h_23 h_1 h_2)) (Litex.number (M := M) (0 : ℂ)) h_47 (Litex.number (M := M) (1 : ℂ)) h_48 h_49 h_50) with ⟨_value_i3, h_26, _value_i4, h_27, h_4, h_5, h_8⟩
            have _exist_match_0 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.sameRefl (Litex.R (M := M)))
            have _exist_match_1 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.sameRefl (Litex.R (M := M)))
            have _exist_match_2 : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (0 : ℂ)))
            have _exist_match_3 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))
            have _exist_match_4 : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (0 : ℂ)))
            have _exist_match_5 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))
            exact ⟨_value_i3, h_26, _value_i4, h_27, h_4, h_5, h_8⟩
          )) with ⟨_value_i5, h_53, _value_i6, h_54, h_55, h_56, h_59⟩
          exact (by
            have _asserted : ((¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ))) ∨ (¬ Litex.Same _value_i6 (Litex.number (M := M) (1 : ℂ)))) := h_59
            have _denied : ¬ (((¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ))) ∨ (¬ Litex.Same _value_i6 (Litex.number (M := M) (1 : ℂ))))) := (by
            classical
            simpa only [not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc] using (show (Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ))) ∧ (Litex.Same _value_i6 (Litex.number (M := M) (1 : ℂ))) from (And.intro h_55 h_56)))
            exact _denied _asserted)
        )
      )
  )

theorem h_269 : ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (_membership_i9 : M.mem (Litex.denote _value_i9) (M.standard Litex.StandardSetValue.real)) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (_membership_i11 : M.mem (Litex.denote _value_i11) (M.standard Litex.StandardSetValue.real)) {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (_membership_i10 : M.mem (Litex.denote _value_i10) (M.standard Litex.StandardSetValue.real)) {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (_membership_i12 : M.mem (Litex.denote _value_i12) (M.standard Litex.StandardSetValue.real)) (h_262 : ((Litex.denote _value_i9) = (M.number (0 : ℂ)))) (h_263 : ((Litex.denote _value_i10) = (M.number (0 : ℂ)))) (h_264 : ((Litex.denote _value_i11) = (M.number (1 : ℂ)))) (h_265 : ((Litex.denote _value_i12) = (M.number (1 : ℂ)))), ((((Litex.denote _value_i9) = (Litex.denote _value_i10))) ∧ (((Litex.denote _value_i11) = (Litex.denote _value_i12)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i9 _rep_i9 _value_i9 _membership_i9 _Host_i11 _rep_i11 _value_i11 _membership_i11 _Host_i10 _rep_i10 _value_i10 _membership_i10 _Host_i12 _rep_i12 _value_i12 _membership_i12 h_262 h_263 h_264 h_265
          have _unique : ∀ (_unique_left_i1 : Litex.Obj (M := M) M.Value) (_member_left_i1 : M.mem (Litex.denote _unique_left_i1) (M.standard Litex.StandardSetValue.real)) (_unique_left_i2 : Litex.Obj (M := M) M.Value) (_member_left_i2 : M.mem (Litex.denote _unique_left_i2) (M.standard Litex.StandardSetValue.real)) (_unique_right_i1 : Litex.Obj (M := M) M.Value) (_member_right_i1 : M.mem (Litex.denote _unique_right_i1) (M.standard Litex.StandardSetValue.real)) (_unique_right_i2 : Litex.Obj (M := M) M.Value) (_member_right_i2 : M.mem (Litex.denote _unique_right_i2) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : ((Litex.denote _unique_left_i1) = (M.number (0 : ℂ)))) (_body_right_0 : ((Litex.denote _unique_right_i1) = (M.number (0 : ℂ)))) (_body_left_1 : ((Litex.denote _unique_left_i2) = (M.number (1 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i2) = (M.number (1 : ℂ)))), (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_left_i1), (Litex.denote _unique_left_i2)]) = (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _unique_right_i1), (Litex.denote _unique_right_i2)]) := ((h_3 (M := M))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i9) (Litex.isSet _value_i9)) _membership_i9 (Litex.semanticObject (Litex.denote _value_i11) (Litex.isSet _value_i11)) _membership_i11 (Litex.semanticObject (Litex.denote _value_i10) (Litex.isSet _value_i10)) _membership_i10 (Litex.semanticObject (Litex.denote _value_i12) (Litex.isSet _value_i12)) _membership_i12 h_262 h_263 h_264 h_265
          exact ⟨(by simpa only [Litex.FiniteFunction.call_tuple, Matrix.cons_val_zero, Matrix.cons_val_succ, Litex.semanticObject_denote] using congrArg (fun t => Litex.FunctionSemantics.callValue (M := M) t (Litex.FiniteFunction.index (0 : Fin 2))) _same), (by simpa only [Litex.FiniteFunction.call_tuple, Matrix.cons_val_zero, Matrix.cons_val_succ, Litex.semanticObject_denote] using congrArg (fun t => Litex.FunctionSemantics.callValue (M := M) t (Litex.FiniteFunction.index (Fin.succ (0 : Fin 1)))) _same)⟩)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_pair_x5f_by_x5f_contradiction_x2f_statement_x2e_lit
