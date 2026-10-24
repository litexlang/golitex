import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_released_x5f_local_x5f_definitions_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.In _value_i1 (Litex.R (M := M))), (by
  let _equal_wd_1_0 := (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_5) (Litex.numberInC (M := M) (0 : ℂ)))
  exact Litex.Same _equal_wd_1_0 _value_i1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5
          have h_19 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          let _object_i2 := (Litex.number (M := M) (2 : ℂ))
          have h_24 : Litex.In _object_i2 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_25 : Litex.Same _object_i2 (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.sameRefl (Litex.number (M := M) (2 : ℂ)))
                )
            )
          have h_26 : Litex.In _object_i2 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_24
                )
            )

          have h_27 : Litex.Same _object_i2 (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  h_25
                )
            )
          let _object_i3 := (Litex.add _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ)))
          have h_55 : Litex.Same _object_i3 (Litex.add _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.sameRefl (Litex.add _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ))))
                )
            )
          have h_56 : Litex.Same _object_i3 (Litex.add _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  h_55
                )
            )
          have h_3 : (by
            let _equal_wd_1_1 := (Litex.add _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ)))
            exact Litex.Same _object_i3 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  h_55
                )
            )
          let _object_w5 := (let _wd_1_0 := (Litex.add _value_i1 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_19) (Litex.numberInC (M := M) (0 : ℂ)));
          let _wd_1_1 := _object_i3;
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.addInC _value_i1 (Litex.number (M := M) (0 : ℂ)) (M.real_subset_complex _ h_19) (Litex.numberInC (M := M) (0 : ℂ)))) (Litex.inOfSame (Litex.add _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ))) _wd_1_1 (Litex.C (M := M)) (Litex.C (M := M)) ((((Litex.sameRefl _wd_1_1)).trans h_55)).symm (Litex.sameRefl (Litex.C (M := M))) (by
            let _atomic_wd_2_0 := (Litex.add _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ)))
            exact (Litex.addInC _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ)))))))

          let _object_w6 := (Litex.add _value_i1 _object_i3 (M.real_subset_complex _ h_19) (Litex.inOfSame (Litex.add _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ))) _object_i3 (Litex.C (M := M)) (Litex.C (M := M)) ((((Litex.sameRefl _object_i3)).trans h_55)).symm (Litex.sameRefl (Litex.C (M := M))) (by
            let _atomic_wd_2_0 := (Litex.add _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ)))
            exact (Litex.addInC _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ))))))

          have h_4 : (by
            let _equal_wd_1_0 := _object_w5
            let _equal_wd_1_1 := _object_w6
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w5;
                  let _equal_wd_1_1 := _object_w6;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19)) + (0 : ℂ)) + (Litex.NativeBridge.asComplex _object_i3 (Litex.inOfSame (Litex.add _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ))) _object_i3 (Litex.C (M := M)) (Litex.C (M := M)) ((((Litex.sameRefl _object_i3)).trans h_55)).symm (Litex.sameRefl (Litex.C (M := M))) (by
                    let _atomic_wd_2_0 := (Litex.add _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ)))
                    exact (Litex.addInC _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ))))))) ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19)) + (Litex.NativeBridge.asComplex _object_i3 (Litex.inOfSame (Litex.add _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ))) _object_i3 (Litex.C (M := M)) (Litex.C (M := M)) ((((Litex.sameRefl _object_i3)).trans h_55)).symm (Litex.sameRefl (Litex.C (M := M))) (by
                    let _atomic_wd_2_0 := (Litex.add _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ)))
                    exact (Litex.addInC _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ))))))) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left _object_i3 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd _value_i1 (Litex.number (M := M) (0 : ℂ)) ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_19)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.asComplex_spec _object_i3 (Litex.inOfSame (Litex.add _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ))) _object_i3 (Litex.C (M := M)) (Litex.C (M := M)) ((((Litex.sameRefl _object_i3)).trans h_55)).symm (Litex.sameRefl (Litex.C (M := M))) (by
                    let _atomic_wd_2_0 := (Litex.add _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ)))
                    exact (Litex.addInC _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ))))))) (Litex.NativeBridge.denoteAdd _value_i1 _object_i3 (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_19)) (Litex.NativeBridge.asComplex_spec _object_i3 (Litex.inOfSame (Litex.add _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ))) _object_i3 (Litex.C (M := M)) (Litex.C (M := M)) ((((Litex.sameRefl _object_i3)).trans h_55)).symm (Litex.sameRefl (Litex.C (M := M))) (by
                    let _atomic_wd_2_0 := (Litex.add _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ)))
                    exact (Litex.addInC _object_i2 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_24) (Litex.numberInC (M := M) (1 : ℂ))))))) (by ring!))))
                )
            )
          exact (let _equal_wd_1_0 := (_object_w5).val.left;
          (show Litex.Same _equal_wd_1_0 _value_i1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19)) + (0 : ℂ)) (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_19)) (Litex.NativeBridge.denoteAdd _value_i1 (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_19)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_19)) (by ring!))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_released_x5f_local_x5f_definitions_x2f_statement_x2e_lit
