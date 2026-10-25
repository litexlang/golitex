import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_abstract_x5f_property_x5f_transport_x2f_statement_x2e_lit

universe u v3 v4 v5 v6 v8
variable {M : Litex.Semantics.{u}}

variable (abstract_prop_1 : (Fin 1 → M.Value) → Prop)

theorem h_4 (abstract_prop_1 : (Fin 1 → M.Value) → Prop) : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_17 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_18 : Litex.In _value_i4 (Litex.R (M := M))) (h_1 : Litex.Same _value_i3 _value_i4) (h_2 : (abstract_prop_1 ![(Litex.denote _value_i3)])), (abstract_prop_1 ![(Litex.denote _value_i4)]) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_17 _Host_i4 _rep_i4 _value_i4 h_18 h_1 h_2
          have h_3 : (abstract_prop_1 ![(Litex.denote _value_i4)]) :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) => (abstract_prop_1 ![_known_argument_0])) (Litex.denote _value_i4)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) => (abstract_prop_1 ![_known_argument_0])) (Litex.denote _value_i3)) := h_2
                    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (abstract_prop_1 ![_known_argument_0])) (Litex.denote _value_i3)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (abstract_prop_1 ![_known_argument_0])) _known_value)) h_1)) _known_citation
                  )
                )
            )
          exact h_3
        )
      )
  )

theorem h_24 (abstract_prop_1 : (Fin 1 → M.Value) → Prop) : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_26 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_27 : Litex.In _value_i6 (Litex.R (M := M))) (h_21 : Litex.Same _value_i5 _value_i6) (h_22 : (abstract_prop_1 ![(Litex.denote _value_i5)])), (abstract_prop_1 ![(Litex.denote _value_i6)]) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_26 _Host_i6 _rep_i6 _value_i6 h_27 h_21 h_22
          have h_29 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_26
                )
            )
          have h_30 : Litex.In _value_i6 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_27
                )
            )
          have h_25 : (abstract_prop_1 ![(Litex.denote _value_i6)]) :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) => (abstract_prop_1 ![_known_argument_0])) (Litex.denote _value_i6)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) => (abstract_prop_1 ![_known_argument_0])) (Litex.denote _value_i5)) := h_22
                    exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (abstract_prop_1 ![_known_argument_0])) (Litex.denote _value_i5)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (abstract_prop_1 ![_known_argument_0])) _known_value)) h_21)) _known_citation
                  )
                )
            )
          exact (show ((fun (_known_argument_0 : M.Value) => (abstract_prop_1 ![_known_argument_0])) (Litex.denote _value_i6)) from by
            have _known_citation : ((fun (_known_argument_0 : M.Value) => (abstract_prop_1 ![_known_argument_0])) (Litex.denote _value_i5)) := h_22
            exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (abstract_prop_1 ![_known_argument_0])) (Litex.denote _value_i5)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (abstract_prop_1 ![_known_argument_0])) _known_value)) h_21)) _known_citation
          )
        )
      )
  )

theorem h_40 (abstract_prop_1 : (Fin 1 → M.Value) → Prop) : ∀ {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_42 : Litex.In _value_i8 (Litex.R (M := M))) (h_38 : (abstract_prop_1 ![(Litex.denote _value_i8)])), (by
  let _atomic_wd_1_0 := (Litex.add _value_i8 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_42) (Litex.numberInC (M := M) (0 : ℂ)))
  exact (abstract_prop_1 ![(Litex.denote _atomic_wd_1_0)])) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i8 _rep_i8 _value_i8 h_42 h_38
          have h_57 : Litex.In _value_i8 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_42
                )
            )
          have h_41 : (by
            have h_58 : Litex.In _value_i8 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_57
                  )
              )
            exact (by
              let _atomic_wd_1_0 := (Litex.add _value_i8 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_58) (Litex.numberInC (M := M) (0 : ℂ)))
              exact (abstract_prop_1 ![(Litex.denote _atomic_wd_1_0)]))
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_58 : Litex.In _value_i8 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_57
                          )
                      )
                    have h_59 : (by
                      let _atomic_wd_1_0 := (Litex.add _value_i8 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_58) (Litex.numberInC (M := M) (0 : ℂ)))
                      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_0 := (Litex.add _value_i8 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_58) (Litex.numberInC (M := M) (0 : ℂ)))
                              exact (Litex.addInR _value_i8 (Litex.number (M := M) (0 : ℂ)) h_58 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))))
                          )
                      )
                    have h_60 : (by
                      let _equal_wd_1_1 := (Litex.add _value_i8 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_58) (Litex.numberInC (M := M) (0 : ℂ)))
                      exact Litex.Same _value_i8 _equal_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.NativeBridge.sameOfDenoteNumber _ _ (Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_57)) ((Litex.NativeBridge.asComplex _value_i8 (Litex.realToComplex _value_i8 h_57)) + (0 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_57)) (Litex.NativeBridge.denoteAdd _value_i8 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_58) (Litex.numberInC (M := M) (0 : ℂ)) _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.realToComplex _value_i8 h_57)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (by ring!))
                          )
                      )
                    have h_61 : (abstract_prop_1 ![(Litex.denote _value_i8)]) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_38
                          )
                      )
                    have h_62 : (abstract_prop_1 ![(Litex.denote (Litex.add _value_i8 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_58) (Litex.numberInC (M := M) (0 : ℂ))))]) :=
                      (by
                        litex_checked_step =>
                          exact (
                            ((h_24 (M := M) abstract_prop_1) _value_i8 h_58 (Litex.add _value_i8 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_58) (Litex.numberInC (M := M) (0 : ℂ))) h_59 h_60 h_61)
                          )
                      )
                    exact (by
                    let _atomic_wd_1_0 := (Litex.add _value_i8 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_58) (Litex.numberInC (M := M) (0 : ℂ)))
                    exact h_62)
                  )
                )
            )
          exact (by
            let _atomic_wd_1_0 := (Litex.add _value_i8 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_57) (Litex.numberInC (M := M) (0 : ℂ)))
            exact h_41)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_abstract_x5f_property_x5f_transport_x2f_statement_x2e_lit
