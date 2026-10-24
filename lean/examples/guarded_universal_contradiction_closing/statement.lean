import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_guarded_x5f_universal_x5f_contradiction_x5f_closing_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_7 : Litex.In _value_i1 (Litex.R (M := M))) (h_1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))), (by
  let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_7) h_1)
  let _equal_wd_1_1 := _equal_wd_1_0
  exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          apply Classical.byContradiction
          intro _litex_negated_goal
          have h_44 : ¬ (∀ (_value_i1 : Litex.Obj (M := M) M.Value), (M.mem (Litex.denote _value_i1) (M.standard Litex.StandardSetValue.real)) → (((¬ ((Litex.denote _value_i1) = (M.number (0 : ℂ))))) → (((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))))) := (by
            classical
            intro _canonical
            apply _litex_negated_goal
            intro _Host_i1 _rep_i1 _value_i1 h_7 h_1
            exact _canonical (Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1)) h_7 h_1)
          have h_83 : (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i1) (M.standard Litex.StandardSetValue.real)), ∃ (h_1 : (¬ ((Litex.denote _value_i1) = (M.number (0 : ℂ))))), (¬ ((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1))))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    have _counterexample : (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i1) (M.standard Litex.StandardSetValue.real)), ∃ (h_1 : (¬ ((Litex.denote _value_i1) = (M.number (0 : ℂ))))), (¬ ((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1))))) := by
                      simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using h_44
                    exact _counterexample)
                )
            )
          exact (by
            have _universal : ∀ {_Host_i2 : Type _} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_96 : Litex.In _value_i2 (Litex.R (M := M))) (h_4 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), (by
            let _object_w7 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_96) h_4)
            exact (by
              let _equal_wd_1_0 := _object_w7
              let _equal_wd_1_1 := _equal_wd_1_0
              exact Litex.Same _equal_wd_1_1 _equal_wd_1_1)
          ) := (by
            intro _Host_i2 _rep_i2 _value_i2 h_96 h_4
            let _object_w7 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_96) h_4)
            have h_5 : (by
              let _equal_wd_1_0 := _object_w7
              let _equal_wd_1_1 := _equal_wd_1_0
              exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show @Eq M.Value _ _ from Eq.refl _)
                  )
              )
            exact h_5
          )
            have _not_universal : ¬ (∀ (_value_i2 : Litex.Obj (M := M) M.Value), (M.mem (Litex.denote _value_i2) (M.standard Litex.StandardSetValue.real)) → (((¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))) → (((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i2)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i2)))))) := (by
            classical
            intro _universal
            have _counterexample : ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_137 : Litex.In _value_i2 (Litex.R (M := M))), ∃ (h_4 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), ¬ Litex.Same (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_137) h_4) (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_137) h_4) := h_83
            rcases _counterexample with ⟨_value_i2, h_137, h_4, h_135⟩
            have _positive : ((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i2)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i2))) := _universal _value_i2 h_137 h_4
            have _negative : (¬ ((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i2)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i2)))) := h_135
            have _refute : ¬ (((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i2)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i2)))) := by
              simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using _negative
            exact _refute _positive)
            apply _not_universal
            intro _closing_i2 _closing_member_i2 h_4
            exact _universal _closing_i2 _closing_member_i2 h_4)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_guarded_x5f_universal_x5f_contradiction_x5f_closing_x2f_statement_x2e_lit
