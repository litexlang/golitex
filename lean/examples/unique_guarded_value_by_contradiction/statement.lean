import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_guarded_x5f_value_x5f_by_x5f_contradiction_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_4 : (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_11 : Litex.In _value_i1 (Litex.R (M := M))), ∃ (h_1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))), ∃ (h_2 : Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ))), Litex.Same (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_11) h_1) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.notSameOfSame _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_2 (show @Eq M.Value _ _ from Eq.refl _) h_1))) ∧ (∀ (_unique_left_i1 : Litex.Obj (M := M) M.Value) (_member_left_i1 : M.mem (Litex.denote _unique_left_i1) (M.standard Litex.StandardSetValue.real)) (_unique_right_i1 : Litex.Obj (M := M) M.Value) (_member_right_i1 : M.mem (Litex.denote _unique_right_i1) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : (¬ ((Litex.denote _unique_left_i1) = (M.number (0 : ℂ))))) (_body_right_0 : (¬ ((Litex.denote _unique_right_i1) = (M.number (0 : ℂ))))) (_body_left_1 : ((Litex.denote _unique_left_i1) = (M.number (2 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i1) = (M.number (2 : ℂ)))) (_body_left_2 : ((M.divValue (M.number (1 : ℂ)) (Litex.denote _unique_left_i1)) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))) (_body_right_2 : ((M.divValue (M.number (1 : ℂ)) (Litex.denote _unique_right_i1)) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))), (Litex.denote _unique_left_i1) = (Litex.denote _unique_right_i1)) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          apply Classical.byContradiction
          intro _litex_negated_goal
          have h_48 : ∀ (_value_i1 : Litex.Obj (M := M) M.Value) (h_49 : Litex.In _value_i1 (Litex.R (M := M))) (h_1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))) (h_2 : Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ))) (h_3 : (by
            let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_49) h_1)
            let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.notSameOfSame _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_2 (show @Eq M.Value _ _ from Eq.refl _) h_1))
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)), ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_81 : Litex.In _value_i4 (Litex.R (M := M))), ∃ (h_44 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))), ∃ (h_45 : Litex.Same _value_i4 (Litex.number (M := M) (2 : ℂ))), ∃ (h_46 : Litex.Same (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_81) h_44) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.notSameOfSame _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_2 (show @Eq M.Value _ _ from Eq.refl _) h_1))), ¬ Litex.Same _value_i4 _value_i1 := (by
            classical
            intro _value_i1 h_49 h_1 h_2 h_3
            apply Classical.byContradiction
            intro _no_alternative
            apply _litex_negated_goal
            constructor
            · exact ⟨(Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1)), h_49, h_1, h_2, h_3⟩
            · intro _unique_left_i1 _member_left_i1 _unique_right_i1 _member_right_i1 _body_left_0 _body_right_0 _body_left_1 _body_right_1 _body_left_2 _body_right_2
              have _same_left_i1 : Litex.denote _unique_left_i1 = Litex.denote _value_i1 := by
                apply Classical.byContradiction
                intro _different
                apply _no_alternative
                exact ⟨_unique_left_i1, _member_left_i1, _body_left_0, _body_left_1, _body_left_2, _different⟩
              have _same_right_i1 : Litex.denote _unique_right_i1 = Litex.denote _value_i1 := by
                apply Classical.byContradiction
                intro _different
                apply _no_alternative
                exact ⟨_unique_right_i1, _member_right_i1, _body_right_0, _body_right_1, _body_right_2, _different⟩
              simp only [_same_left_i1, _same_right_i1])
          rcases (show ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_113 : Litex.In _value_i2 (Litex.R (M := M))), ∃ (h_5 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), ∃ (h_6 : Litex.Same _value_i2 (Litex.number (M := M) (2 : ℂ))), ∃ (h_7 : Litex.Same (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_113) h_5) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.notSameOfSame _value_i2 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_6 (show @Eq M.Value _ _ from Eq.refl _) h_5))), ¬ Litex.Same _value_i2 (Litex.number (M := M) (2 : ℂ)) from (by
            have h_166 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
              (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
            have h_167 : ¬ Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
              (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))
            have h_168 : Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
              (show @Eq M.Value _ _ from Eq.refl _)
            have h_169 : (by
              let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              let _equal_wd_1_1 := _equal_wd_1_0
              exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) :=
              (show @Eq M.Value _ _ from Eq.refl _)
            rcases ((show ∀ {_Host_i1 : Type _} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_49 : Litex.In _value_i1 (Litex.R (M := M))) (h_1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))) (h_2 : Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ))) (h_3 : (by
              let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_49) h_1)
              let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.notSameOfSame _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_2 (show @Eq M.Value _ _ from Eq.refl _) h_1))
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)), ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_81 : Litex.In _value_i4 (Litex.R (M := M))), ∃ (h_44 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ))), ∃ (h_45 : Litex.Same _value_i4 (Litex.number (M := M) (2 : ℂ))), ∃ (h_46 : Litex.Same (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_81) h_44) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.notSameOfSame _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_2 (show @Eq M.Value _ _ from Eq.refl _) h_1))), ¬ Litex.Same _value_i4 _value_i1 from (fun {_Host_i1 : Type _} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_49 : Litex.In _value_i1 (Litex.R (M := M))) (h_1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))) (h_2 : Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ))) (h_3 : (by
              let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_49) h_1)
              let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.notSameOfSame _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_2 (show @Eq M.Value _ _ from Eq.refl _) h_1))
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) => by
              exact h_48 (Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1)) h_49 h_1 h_2 h_3)) (Litex.number (M := M) (2 : ℂ)) h_166 h_167 h_168 h_169) with ⟨_value_i2, h_113, h_5, h_6, h_7, h_8⟩
            have _exist_match_0 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.sameRefl (Litex.R (M := M)))
            have _exist_match_1 : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (0 : ℂ)))
            have _exist_match_2 : Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (2 : ℂ)))
            have _exist_match_3 : Litex.Same (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_113) h_5) (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_113) h_5) := (Litex.sameRefl (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_113) h_5))
            have _exist_match_4 : Litex.Same (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.notSameOfSame _value_i2 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_6 (show @Eq M.Value _ _ from Eq.refl _) h_5)) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.notSameOfSame _value_i2 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_6 (show @Eq M.Value _ _ from Eq.refl _) h_5)) := (Litex.sameRefl (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.notSameOfSame _value_i2 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_6 (show @Eq M.Value _ _ from Eq.refl _) h_5)))
            have _exist_match_5 : Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) := (Litex.sameRefl (Litex.number (M := M) (2 : ℂ)))
            exact ⟨_value_i2, h_113, h_5, h_6, h_7, h_8⟩
          )) with ⟨_value_i3, h_178, h_179, h_180, h_181, h_182⟩
          exact (by
            have _asserted : Litex.Same _value_i3 (Litex.number (M := M) (2 : ℂ)) := h_180
            have _denied : ¬ (Litex.Same _value_i3 (Litex.number (M := M) (2 : ℂ))) := h_182
            exact _denied _asserted)
        )
      )
  )

theorem h_232 : ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (_membership_i5 : M.mem (Litex.denote _value_i5) (M.standard Litex.StandardSetValue.real)) {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (_membership_i6 : M.mem (Litex.denote _value_i6) (M.standard Litex.StandardSetValue.real)) (h_225 : (¬ ((Litex.denote _value_i5) = (M.number (0 : ℂ))))) (h_226 : (¬ ((Litex.denote _value_i6) = (M.number (0 : ℂ))))) (h_227 : ((Litex.denote _value_i5) = (M.number (2 : ℂ)))) (h_228 : ((Litex.denote _value_i6) = (M.number (2 : ℂ)))) (h_229 : ((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i5)) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))) (h_230 : ((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))), ((Litex.denote _value_i5) = (Litex.denote _value_i6)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 _membership_i5 _Host_i6 _rep_i6 _value_i6 _membership_i6 h_225 h_226 h_227 h_228 h_229 h_230
          have _unique : ∀ (_unique_left_i1 : Litex.Obj (M := M) M.Value) (_member_left_i1 : M.mem (Litex.denote _unique_left_i1) (M.standard Litex.StandardSetValue.real)) (_unique_right_i1 : Litex.Obj (M := M) M.Value) (_member_right_i1 : M.mem (Litex.denote _unique_right_i1) (M.standard Litex.StandardSetValue.real)) (_body_left_0 : (¬ ((Litex.denote _unique_left_i1) = (M.number (0 : ℂ))))) (_body_right_0 : (¬ ((Litex.denote _unique_right_i1) = (M.number (0 : ℂ))))) (_body_left_1 : ((Litex.denote _unique_left_i1) = (M.number (2 : ℂ)))) (_body_right_1 : ((Litex.denote _unique_right_i1) = (M.number (2 : ℂ)))) (_body_left_2 : ((M.divValue (M.number (1 : ℂ)) (Litex.denote _unique_left_i1)) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))) (_body_right_2 : ((M.divValue (M.number (1 : ℂ)) (Litex.denote _unique_right_i1)) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))))), (Litex.denote _unique_left_i1) = (Litex.denote _unique_right_i1) := ((h_4 (M := M))).2
          have _same := _unique (Litex.semanticObject (Litex.denote _value_i5) (Litex.isSet _value_i5)) _membership_i5 (Litex.semanticObject (Litex.denote _value_i6) (Litex.isSet _value_i6)) _membership_i6 h_225 h_226 h_227 h_228 h_229 h_230
          exact _same)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_unique_x5f_guarded_x5f_value_x5f_by_x5f_contradiction_x2f_statement_x2e_lit
