import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_cotangent_x5f_nonzero_x5f_from_x5f_cosine_x5f_reversed_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.In _value_i1 (Litex.R (M := M))) (h_1 : (by
  let _atomic_wd_1_0 := (Litex.sin _value_i1 h_6)
  exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))) (h_2 : (by
  let _atomic_wd_1_0 := (Litex.cos _value_i1 h_6)
  exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))), ¬ Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.cot _value_i1 h_6 (by
  let _atomic_wd_1_0 := (Litex.sin _value_i1 h_6)
  exact h_1)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 h_1 h_2
          have h_30 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          let _object_w9 := (Litex.cot _value_i1 h_30 (by
            let _atomic_wd_1_0 := (Litex.sin _value_i1 h_30)
            exact h_1))

          have h_5 : (by
            let _atomic_wd_1_1 := _object_w9
            exact ¬ Litex.Same (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w9
                    exact (let _quotient := _atomic_wd_1_1; let _numerator := (Litex.cos _value_i1 h_30); fun _litex_equal => (Litex.cotNonzeroOfCos _quotient _numerator rfl (fun _known_equal => h_2 (_known_equal.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))).symm))) ((_litex_equal.symm).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          exact (by
            let _atomic_wd_1_1 := _object_w9
            exact h_5)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_cotangent_x5f_nonzero_x5f_from_x5f_cosine_x5f_reversed_x2f_statement_x2e_lit
