import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_weaken_x5f_numeric_x5f_upper_x5f_bounds_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.In _value_i1 (Litex.R (M := M))) (h_1 : Litex.Lt _value_i1 (Litex.number (M := M) (4 : ℂ))), ((Litex.Le _value_i1 (Litex.number (M := M) (6 : ℂ))) ∧ (Litex.Lt _value_i1 (Litex.number (M := M) (6 : ℂ)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_17 h_1
          have h_2 : Litex.Le _value_i1 (Litex.number (M := M) (6 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.leTrans _value_i1 (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (Litex.ltToLe _value_i1 (Litex.number (M := M) (4 : ℂ)) h_1) (Litex.NativeBridge.leOfDenoteReal (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (4 : ℝ) (6 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))) (((Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))).trans (congrArg M.number (by norm_num))) (by norm_num)))
                )
            )
          have h_3 : Litex.Lt _value_i1 (Litex.number (M := M) (6 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltLeTrans _value_i1 (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (6 : ℂ)) h_1 (Litex.NativeBridge.leOfDenoteReal (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (4 : ℝ) (6 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))) (((Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))).trans (congrArg M.number (by norm_num))) (by norm_num)))
                )
            )
          exact (And.intro h_2 h_3)
        )
      )
  )

theorem h_211 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_225 : Litex.In _value_i2 (Litex.R (M := M))) (h_208 : Litex.Le _value_i2 (Litex.number (M := M) (4 : ℂ))), ((Litex.Le _value_i2 (Litex.number (M := M) (6 : ℂ))) ∧ (Litex.Lt _value_i2 (Litex.number (M := M) (6 : ℂ)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_225 h_208
          have h_209 : Litex.Le _value_i2 (Litex.number (M := M) (6 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.leTrans _value_i2 (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (6 : ℂ)) h_208 (Litex.NativeBridge.leOfDenoteReal (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (4 : ℝ) (6 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))) (((Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))).trans (congrArg M.number (by norm_num))) (by norm_num)))
                )
            )
          have h_210 : Litex.Lt _value_i2 (Litex.number (M := M) (6 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.leLtTrans _value_i2 (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (6 : ℂ)) h_208 (Litex.NativeBridge.ltOfDenoteReal (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (4 : ℝ) (6 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num))) (((Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))).trans (congrArg M.number (by norm_num))) (by norm_num)))
                )
            )
          exact (And.intro h_209 h_210)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_weaken_x5f_numeric_x5f_upper_x5f_bounds_x2f_statement_x2e_lit
