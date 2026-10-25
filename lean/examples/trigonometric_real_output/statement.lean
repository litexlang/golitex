import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_trigonometric_x5f_real_x5f_output_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.R (M := M))), (by
  let _object_w2 := (Litex.sin _value_i1 h_16)
  let _object_w3 := (Litex.cos _value_i1 h_16)
  exact (((by
    let _atomic_wd_1_0 := _object_w2
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))) ∧ ((by
    let _atomic_wd_1_0 := _object_w3
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_16
          let _object_w2 := (Litex.sin _value_i1 h_16)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w2
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    exact (Litex.sinInR _atomic_wd_1_0))
                )
            )
          let _object_w3 := (Litex.cos _value_i1 h_16)
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w3
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    exact (Litex.cosInR _atomic_wd_1_0))
                )
            )
          exact (And.intro h_1 h_2)
        )
      )
  )

theorem h_43 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_56 : Litex.In _value_i2 (Litex.R (M := M))) (h_41 : (by
  let _atomic_wd_1_0 := (Litex.cos _value_i2 h_56)
  exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))), (by
  let _object_w7 := (Litex.tan _value_i2 h_56 (by
    let _atomic_wd_1_0 := (Litex.cos _value_i2 h_56)
    exact h_41))
  exact (by
    let _atomic_wd_1_0 := _object_w7
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_56 h_41
          let _object_w7 := (Litex.tan _value_i2 h_56 (by
            let _atomic_wd_1_0 := (Litex.cos _value_i2 h_56)
            exact h_41))
          have h_42 : (by
            let _atomic_wd_1_0 := _object_w7
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w7
                    exact (Litex.tanInR _atomic_wd_1_0))
                )
            )
          exact h_42
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_trigonometric_x5f_real_x5f_output_x2f_statement_x2e_lit
