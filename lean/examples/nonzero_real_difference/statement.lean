import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_real_x5f_difference_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.R (M := M))) (h_1 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ))), (by
  let _object_w3 := (Litex.sub _value_i1 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_16) (Litex.numberInC (M := M) (1 : ℂ)))
  exact (by
    let _atomic_wd_1_0 := _object_w3
    exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))
) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_16 h_1
    let _object_w3 := (Litex.sub _value_i1 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_16) (Litex.numberInC (M := M) (1 : ℂ)))
    have h_2 : (by
      let _atomic_wd_1_0 := _object_w3
      exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_0 := _object_w3
              exact (fun _litex_equal => (Litex.subNonzeroOfNotSame _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i1 h_16) (Litex.numberInC (M := M) (1 : ℂ)) h_1) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
          )
      )
    exact h_2
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_real_x5f_difference_x2f_statement_x2e_lit
