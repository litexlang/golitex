import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_released_x5f_witness_x5f_definition_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_3 : Litex.In _value_i1 (Litex.R (M := M))), Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        by
          let _value_i1 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.isSet (Litex.number (M := M) (2 : ℂ)))
          have h_5 : Litex.In _value_i1 (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
          have h_6 : Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ)) := rfl
          have h_7 : Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
          exact ⟨_value_i1, h_5, h_7⟩
      )
  )

noncomputable def _value_i2 : Litex.Obj (M := M) M.Value :=
  Classical.choose ((show ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_11 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same _value_i2 (Litex.number (M := M) (2 : ℂ)) from ⟨Litex.semanticObject (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.isSet (Litex.number (M := M) (2 : ℂ))), (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), (by rfl)⟩))

theorem h_13 : Litex.In (_value_i2 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((show ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_11 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same _value_i2 (Litex.number (M := M) (2 : ℂ)) from ⟨Litex.semanticObject (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.isSet (Litex.number (M := M) (2 : ℂ))), (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), (by rfl)⟩)))))
      )
  )

theorem h_9 : Litex.Same (_value_i2 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec ((show ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_11 : Litex.In _value_i2 (Litex.R (M := M))), Litex.Same _value_i2 (Litex.number (M := M) (2 : ℂ)) from ⟨Litex.semanticObject (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.isSet (Litex.number (M := M) (2 : ℂ))), (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)), (by rfl)⟩)))))
      )
  )

theorem h_14 : Litex.In (_value_i2 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (h_13 (M := M))
      )
  )

theorem h_15 : Litex.Same (_value_i2 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (h_9 (M := M))
      )
  )

noncomputable def _object_w9 := (Litex.add (_value_i2 (M := M)) (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_13 (M := M))) (Litex.numberInC (M := M) (1 : ℂ)))

theorem h_16 : (by
  let _equal_wd_1_0 := (_object_w9 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (((congrArg₂ M.addValue (h_9 (M := M)) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))))).trans (((let _equal_wd_2_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
        (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) ((2 : ℂ) + (1 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))))).trans ((Litex.sameRefl (Litex.number (M := M) (3 : ℂ)))).symm))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_released_x5f_witness_x5f_definition_x2f_statement_x2e_lit
