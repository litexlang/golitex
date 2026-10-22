import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nested_x5f_named_x5f_add_x5f_zero_x2f_statement_x2e_lit

universe u v1 v3
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_3 : Litex.In _value_i1 (Litex.R (M := M))), (by
  let _equal_wd_1_0 := (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_3) (Litex.numberInC (M := M) (0 : ℂ)))
  exact Litex.Same _equal_wd_1_0 _value_i1) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_3
    have h_17 : Litex.In _value_i1 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_3
          )
      )
    exact (let _equal_wd_1_0 := (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_17) (Litex.numberInC (M := M) (0 : ℂ)));
    (show Litex.Same _equal_wd_1_0 _value_i1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_17)) + (0 : ℂ)) (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_17)) (Litex.NativeBridge.denoteAdd _value_i1 (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_17)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_17)) (by ring!))))
  )

theorem h_48 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_50 : Litex.In _value_i3 (Litex.R (M := M))), (by
  let _equal_wd_1_0 := (Litex.add _value_i3 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_50) (Litex.numberInC (M := M) (0 : ℂ)))
  exact Litex.Same _equal_wd_1_0 _value_i3) :=
  (by
    intro _Host_i3 _rep_i3 _value_i3 h_50
    have h_64 : Litex.In _value_i3 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            h_50
          )
      )
    have h_49 : (by
      have h_65 : Litex.In _value_i3 (Litex.R (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              h_64
            )
        )
      exact (by
        let _equal_wd_1_0 := (Litex.add _value_i3 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_65) (Litex.numberInC (M := M) (0 : ℂ)))
        exact Litex.Same _equal_wd_1_0 _value_i3)
    ) :=
      (by
        litex_checked_step =>
          exact (
            (by
              have h_65 : Litex.In _value_i3 (Litex.R (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      h_64
                    )
                )
              have h_66 : Litex.Same (Litex.add _value_i3 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_65) (Litex.numberInC (M := M) (0 : ℂ))) _value_i3 :=
                (by
                  litex_checked_step =>
                    exact (
                      ((h_2 (M := M)) _value_i3 h_65)
                    )
                )
              exact (let _equal_wd_1_0 := (Litex.add _value_i3 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_65) (Litex.numberInC (M := M) (0 : ℂ)));
            (show Litex.Same _equal_wd_1_0 _value_i3 from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_66).trans (Litex.sameRefl _value_i3)))))
            )
          )
      )
    exact h_49
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nested_x5f_named_x5f_add_x5f_zero_x2f_statement_x2e_lit
