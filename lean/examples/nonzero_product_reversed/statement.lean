import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_product_x5f_reversed_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.In _value_i1 (Litex.C (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_6 : Litex.In _value_i2 (Litex.C (M := M))) (h_1 : (by
  let _atomic_wd_1_1 := (Litex.mul _value_i1 _value_i2 h_5 h_6)
  exact ¬ Litex.Same (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1)), ¬ Litex.Same (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 _Host_i2 _rep_i2 _value_i2 h_6 h_1
          have h_21 : Litex.In _value_i1 (Litex.C (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          have h_22 : Litex.In _value_i2 (Litex.C (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_4 : ¬ Litex.Same (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_equal => (Litex.productNonzeroFactors (Litex.mul _value_i1 _value_i2 h_21 h_22) (fun _product_eq => h_1 (_product_eq.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))).symm).symm)).2 ((_litex_equal.symm).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ))))))
                )
            )
          exact h_4
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_product_x5f_reversed_x2f_statement_x2e_lit
