import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_reciprocal_x5f_counterexample_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_4 : Litex.In _value_i1 (Litex.R (M := M))), ∃ (h_1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))), ¬ Litex.Same (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_4) h_1) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        by
          let _value_i1 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (1 : ℂ))) (Litex.isSet (Litex.number (M := M) (1 : ℂ)))
          have h_25 : Litex.In _value_i1 (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
          have h_26 : Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)) := rfl
          have h_27 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))
          have h_28 : (by
            let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ))) := (by
            let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) ((1 : ℂ) / (1 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)))
          exact ⟨_value_i1, h_25, h_27, h_28⟩
      )
  )

theorem h_42 : ¬ (∀ (_value_i2 : Litex.Obj (M := M) M.Value), (M.mem (Litex.denote _value_i2) (M.standard Litex.StandardSetValue.real)) → (((¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))) → (((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i2)) = (M.number (2 : ℂ)))))) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          intro _universal
          have _counterexample : ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_45 : Litex.In _value_i2 (Litex.R (M := M))), ∃ (h_40 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), ¬ Litex.Same (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_45) h_40) (Litex.number (M := M) (2 : ℂ)) := (h_3 (M := M))
          rcases _counterexample with ⟨_value_i2, h_45, h_40, h_43⟩
          have _positive : ((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i2)) = (M.number (2 : ℂ))) := _universal _value_i2 h_45 h_40
          have _negative : (¬ ((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i2)) = (M.number (2 : ℂ)))) := h_43
          have _refute : ¬ (((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i2)) = (M.number (2 : ℂ)))) := by
            simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using _negative
          exact _refute _positive)
      )
  )

theorem h_66 : ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_45 : Litex.In _value_i2 (Litex.R (M := M))), ∃ (h_40 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), ¬ Litex.Same (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (M.real_subset_complex _ h_45) h_40) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          have _counterexample : (∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i2) (M.standard Litex.StandardSetValue.real)), ∃ (h_40 : (¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))), (¬ ((M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i2)) = (M.number (2 : ℂ))))) := by
            simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using (h_42 (M := M))
          exact _counterexample)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_reciprocal_x5f_counterexample_x2f_statement_x2e_lit
