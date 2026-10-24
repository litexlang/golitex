import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_contradiction_x5f_with_x5f_reciprocal_x5f_guard_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_8 : Litex.In _value_i1 (Litex.R (M := M))) (h_1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))), (by
  let _equal_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_8) h_1)
  let _equal_wd_1_1 := _equal_wd_1_0
  exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          apply Classical.byContradiction
          intro _litex_negated_goal
          have h_45 : ¬ (∀ (_value_i1 : Litex.Obj (M := M) M.Value), (M.mem (Litex.denote _value_i1) (M.standard Litex.StandardSetValue.real)) → (((¬ ((Litex.denote _value_i1) = (M.number (0 : ℂ))))) → (((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)))))) := (by
            classical
            intro _canonical
            apply _litex_negated_goal
            intro _Host_i1 _rep_i1 _value_i1 h_8 h_1
            exact _canonical (Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1)) h_8 h_1)
          have h_84 : (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i1) (M.standard Litex.StandardSetValue.real)), ∃ (h_1 : (¬ ((Litex.denote _value_i1) = (M.number (0 : ℂ))))), (¬ ((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1))))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    have _counterexample : (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i1) (M.standard Litex.StandardSetValue.real)), ∃ (h_1 : (¬ ((Litex.denote _value_i1) = (M.number (0 : ℂ))))), (¬ ((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i1))))) := by
                      simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using h_45
                    exact _counterexample)
                )
            )
          rcases (show ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_85 : Litex.In _value_i2 (Litex.R (M := M))), ∃ (h_4 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), ¬ Litex.Same (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_85) h_4) (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_85) h_4) from h_84) with ⟨_value_i3, h_123, h_124, h_125⟩
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
end LitexCompiled.file_lean_x2f_examples_x2f_contradiction_x5f_with_x5f_reciprocal_x5f_guard_x2f_statement_x2e_lit
