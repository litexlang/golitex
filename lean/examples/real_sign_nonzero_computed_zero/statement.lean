import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_sign_x5f_nonzero_x5f_computed_x5f_zero_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.In _value_i1 (Litex.R (M := M))) (h_1 : (by
  let _atomic_wd_1_1 := (Litex.sub (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
  exact ¬ Litex.Same _value_i1 _atomic_wd_1_1)), ¬ Litex.Same (Litex.sign _value_i1 h_5) (Litex.sub (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 h_1
          have h_18 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          let _object_w5 := (Litex.sign _value_i1 h_18)

          have h_4 : (by
            let _atomic_wd_1_0 := _object_w5
            let _atomic_wd_1_1 := (Litex.sub (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
            exact ¬ Litex.Same _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w5
                    let _atomic_wd_1_1 := (Litex.sub (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
                    exact (fun _litex_equal => (fun _known_equal => h_1 (_known_equal.trans (((Litex.NativeBridge.denoteSub (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) - (1 : ℂ)) = (0 : ℂ)))).symm)) ((Litex.signZeroIffArgZero _atomic_wd_1_0 (_atomic_wd_1_0).wd).mp ((_litex_equal).trans (((Litex.NativeBridge.denoteSub (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) - (1 : ℂ)) = (0 : ℂ))))))))
                )
            )
          exact (by
            let _atomic_wd_1_0 := _object_w5
            let _atomic_wd_1_1 := (Litex.sub (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))
            exact h_4)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_sign_x5f_nonzero_x5f_computed_x5f_zero_x2f_statement_x2e_lit
