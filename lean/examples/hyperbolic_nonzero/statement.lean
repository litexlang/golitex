import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_hyperbolic_x5f_nonzero_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.R (M := M))), (by
  let _object_w2 := (Litex.cosh _value_i1 h_16)
  let _object_w4 := (Litex.sech _value_i1 h_16)
  exact (((by
    let _atomic_wd_1_0 := _object_w2
    exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))) ∧ ((by
    let _atomic_wd_1_0 := _object_w4
    exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_16
          let _object_w2 := (Litex.cosh _value_i1 h_16)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w2
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    exact (fun _same => (Litex.coshNonzero _atomic_wd_1_0) (_same.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          let _object_w4 := (Litex.sech _value_i1 h_16)
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w4
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w4
                    exact (fun _same => (Litex.sechNonzero _atomic_wd_1_0) (_same.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          exact (And.intro h_1 h_2)
        )
      )
  )

theorem h_51 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_64 : Litex.In _value_i2 (Litex.R (M := M))) (h_46 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w7 := (Litex.sinh _value_i2 h_64)
  let _object_w8 := (Litex.coth _value_i2 h_64 h_46)
  let _object_w9 := (Litex.csch _value_i2 h_64 h_46)
  let _object_w10 := (Litex.neg _value_i2 (M.real_subset_complex _ h_64))
  exact (((by
    let _atomic_wd_1_0 := _object_w7
    exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))) ∧ ((((by
    let _atomic_wd_1_0 := _object_w8
    exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))) ∧ ((((by
    let _atomic_wd_1_0 := _object_w9
    exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))) ∧ ((by
    let _atomic_wd_1_0 := _object_w10
    exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_64 h_46
          let _object_w7 := (Litex.sinh _value_i2 h_64)
          have h_47 : (by
            let _atomic_wd_1_0 := _object_w7
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w7
                    exact (fun _same => (Litex.sinhNonzero _atomic_wd_1_0 h_46) (_same.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          let _object_w8 := (Litex.coth _value_i2 h_64 h_46)
          have h_48 : (by
            let _atomic_wd_1_0 := _object_w8
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w8
                    exact (fun _same => (Litex.cothNonzero _atomic_wd_1_0) (_same.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          let _object_w9 := (Litex.csch _value_i2 h_64 h_46)
          have h_49 : (by
            let _atomic_wd_1_0 := _object_w9
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w9
                    exact (fun _same => (Litex.cschNonzero _atomic_wd_1_0) (_same.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          let _object_w10 := (Litex.neg _value_i2 (M.real_subset_complex _ h_64))
          have h_50 : (by
            let _atomic_wd_1_0 := _object_w10
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w10
                    exact (by
                      have _premise : ¬ Litex.Same _value_i2 (Litex.number (M := M) 0) := fun h => h_46 (h.trans ((((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ))))).symm)
                      have _native := Litex.NativeBridge.nativeNonzeroOfDenote _value_i2 (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_64)) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_64)) _premise
                      have _negated := Litex.NativeBridge.notSameOfNativeNonzero _atomic_wd_1_0 (- (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_64))) (Litex.NativeBridge.denoteNeg _value_i2 (_atomic_wd_1_0).wd _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_64))) (by simpa only [neg_ne_zero] using _native)
                      exact fun h => _negated (h.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          exact (And.intro h_47 (And.intro h_48 (And.intro h_49 h_50)))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_hyperbolic_x5f_nonzero_x2f_statement_x2e_lit
