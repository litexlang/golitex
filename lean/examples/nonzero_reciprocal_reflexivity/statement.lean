import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_reciprocal_x5f_reflexivity_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

theorem h_3 : ¬ (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_8 : Litex.In _value_i1 (Litex.R (M := M))), ∃ (h_1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))), ¬ Litex.Same (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_8) h_1) (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_8) h_1)) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          apply Classical.byContradiction
          intro _litex_negated_goal
          have h_46 : ∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_47 : Litex.In _value_i1 (Litex.R (M := M))), ∃ (h_1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))), ¬ Litex.Same (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_47) h_1) (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_47) h_1) := (by
            classical
            simpa only [not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc] using _litex_negated_goal)
          rcases (show ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_85 : Litex.In _value_i2 (Litex.R (M := M))), ∃ (h_4 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), ¬ Litex.Same (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_85) h_4) (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_85) h_4) from h_46) with ⟨_value_i3, h_123, h_124, h_125⟩
          exact (by
            have _asserted : (by
            let _equal_wd_1_0 := ((fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_85 : Litex.In _value_i2 (Litex.R (M := M))) (h_4 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))) => (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_85) h_4)) _value_i3 h_123 h_124)
            let _equal_wd_1_1 := _equal_wd_1_0
            exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) := (show @Eq M.Value _ _ from Eq.refl _)
            have _denied : ¬ ((by
            let _equal_wd_1_0 := ((fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_85 : Litex.In _value_i2 (Litex.R (M := M))) (h_4 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))) => (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_85) h_4)) _value_i3 h_123 h_124)
            let _equal_wd_1_1 := _equal_wd_1_0
            exact Litex.Same _equal_wd_1_1 _equal_wd_1_1)) := (by
            let _atomic_wd_1_0 := ((fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_85 : Litex.In _value_i2 (Litex.R (M := M))) (h_4 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))) => (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_85) h_4)) _value_i3 h_123 h_124)
            let _atomic_wd_1_1 := _atomic_wd_1_0
            exact h_125)
            exact _denied _asserted)
        )
      )
  )

theorem h_177 : ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (_membership_i4 : M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)), ((((Litex.denote _value_i4) = (M.number (0 : ℂ)))) ∨ (((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i4)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i4))))) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          intro _Host_i4 _rep_i4 _value_i4 _membership_i4
          have _excluded : ¬ ((∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i1) (M.standard Litex.StandardSetValue.real)), ∃ (h_1 : (¬ ((Litex.denote _value_i1) = (M.number (0 : ℂ))))), (¬ ((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))))) := (h_3 (M := M))
          have _no_body : ¬ ((((¬ ((Litex.denote _value_i4) = (M.number (0 : ℂ))))) ∧ ((¬ ((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i4)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i4))))))) := by
            intro _candidate
            rcases _candidate with ⟨h_1, h_2⟩
            apply _excluded
            exact ⟨Litex.semanticObject (Litex.denote _value_i4) (Litex.isSet _value_i4), _membership_i4, h_1, h_2⟩
          simpa only [not_and_or, not_or, not_not, and_assoc, or_assoc] using _no_body)
      )
  )

theorem h_180 : ¬ (∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (h_181 : Litex.In _value_i5 (Litex.R (M := M))), ∃ (h_178 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ))), ¬ Litex.Same (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_181) h_178) (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i5 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_181) h_178)) :=
  (by
    litex_complete =>
      exact (
        (h_3 (M := M))
      )
  )

theorem h_224 : ∀ {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (_membership_i6 : M.mem (Litex.denote _value_i6) (M.standard Litex.StandardSetValue.real)), ((((Litex.denote _value_i6) = (M.number (0 : ℂ)))) ∨ (((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6))))) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          intro _Host_i6 _rep_i6 _value_i6 _membership_i6
          have _excluded : ¬ ((∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i5) (M.standard Litex.StandardSetValue.real)), ∃ (h_178 : (¬ ((Litex.denote _value_i5) = (M.number (0 : ℂ))))), (¬ ((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i5)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i5)))))) := (h_180 (M := M))
          have _no_body : ¬ ((((¬ ((Litex.denote _value_i6) = (M.number (0 : ℂ))))) ∧ ((¬ ((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6))))))) := by
            intro _candidate
            rcases _candidate with ⟨h_178, h_179⟩
            apply _excluded
            exact ⟨Litex.semanticObject (Litex.denote _value_i6) (Litex.isSet _value_i6), _membership_i6, h_178, h_179⟩
          simpa only [not_and_or, not_or, not_not, and_assoc, or_assoc] using _no_body)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_reciprocal_x5f_reflexivity_x2f_statement_x2e_lit
