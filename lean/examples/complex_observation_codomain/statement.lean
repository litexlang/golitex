import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_observation_x5f_codomain_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_18 : Litex.In _value_i1 (Litex.C (M := M))), (by
  let _object_w2 := (Litex.conj _value_i1 h_18)
  let _object_w3 := (Litex.re _value_i1 h_18)
  let _object_w5 := (Litex.img _value_i1 h_18)
  let _object_w6 := (Litex.complexAbs _value_i1 h_18)
  exact (((by
    let _atomic_wd_1_0 := _object_w2
    exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))) ∧ ((((by
    let _atomic_wd_1_0 := _object_w3
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))) ∧ ((((by
    let _atomic_wd_1_0 := _object_w5
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))) ∧ ((by
    let _atomic_wd_1_0 := _object_w6
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_18
          let _object_w2 := (Litex.conj _value_i1 h_18)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w2
            exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    exact (Litex.conjInC _atomic_wd_1_0))
                )
            )
          let _object_w3 := (Litex.re _value_i1 h_18)
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w3
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    exact (Litex.reInR _atomic_wd_1_0))
                )
            )
          let _object_w5 := (Litex.img _value_i1 h_18)
          have h_3 : (by
            let _atomic_wd_1_0 := _object_w5
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w5
                    exact (Litex.imgInR _atomic_wd_1_0))
                )
            )
          let _object_w6 := (Litex.complexAbs _value_i1 h_18)
          have h_4 : (by
            let _atomic_wd_1_0 := _object_w6
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w6
                    exact (Litex.complexAbsInR _atomic_wd_1_0))
                )
            )
          exact (And.intro h_1 (And.intro h_2 (And.intro h_3 h_4)))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_observation_x5f_codomain_x2f_statement_x2e_lit
