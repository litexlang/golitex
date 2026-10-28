import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_power_x5f_nonzero_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_1 : Litex.IsNonempty (Litex.Z (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.integer)

variable {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.Z (M := M)))

theorem h_5 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.Z (M := M))) : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_7 : Litex.In _value_i2 (Litex.C (M := M))) (h_3 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), ¬ Litex.Same (Litex.powInt _value_i2 _value_i1 (Classical.choose ((M.integer_members (Litex.denote _value_i1)).mp h_2)) h_7 h_2 h_3 (Classical.choose_spec ((M.integer_members (Litex.denote _value_i1)).mp h_2))) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_7 h_3
          have h_2901 : Litex.In _value_i2 (Litex.C (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          let _object_w6 := (Litex.powInt _value_i2 _value_i1 (Classical.choose ((M.integer_members (Litex.denote _value_i1)).mp h_2)) h_2901 h_2 h_3 (Classical.choose_spec ((M.integer_members (Litex.denote _value_i1)).mp h_2)))

          have h_6 : (by
            let _atomic_wd_1_0 := _object_w6
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w6
                    exact (fun _litex_equal => (Litex.powNonzeroOfBase _atomic_wd_1_0 h_2 h_3) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          exact (by
            let _atomic_wd_1_0 := _object_w6
            exact h_6)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_power_x5f_nonzero_x5f_theorem_x2f_statement_x2e_lit
