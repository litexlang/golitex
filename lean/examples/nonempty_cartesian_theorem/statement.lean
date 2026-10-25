import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nonempty_x5f_cartesian_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.IsNonempty _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_5 : Litex.IsNonempty _value_i2), (by
  let _atomic_wd_1_0 := (Litex.cart (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i))))
  exact Litex.IsNonempty _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4 _Host_i2 _rep_i2 _value_i2 h_5
          have h_8 : Litex.IsNonempty _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_4
                )
            )
          have h_9 : Litex.IsNonempty _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          let _object_w1 := (Litex.cart (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i))))

          have h_3 : (by
            let _atomic_wd_1_0 := _object_w1
            exact Litex.IsNonempty _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w1
                    exact (Litex.cartNonemptyOfFactors _atomic_wd_1_0 (by
                      have _finiteProof_0 := (h_8)
                      have _finiteProof_1 := (h_9)
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )))
                )
            )
          exact (by
            let _atomic_wd_1_0 := _object_w1
            exact h_3)
        )
      )
  )

theorem h_36 : (by
  let _atomic_wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.C (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.C (M := M))) (fun i => Fin.elim0 i))))
  exact Litex.IsNonempty _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_37 : Litex.IsNonempty (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)
                )
            )
          have h_38 : Litex.IsNonempty (Litex.C (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.standardNonempty (M := M) Litex.StandardSetValue.complex)
                )
            )
          have h_39 : Litex.IsNonempty (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.C (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.C (M := M))) (fun i => Fin.elim0 i)))) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_2 (M := M)) (Litex.R (M := M)) h_37 (Litex.C (M := M)) h_38)
                )
            )
          exact (by
          let _atomic_wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.C (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.C (M := M))) (fun i => Fin.elim0 i))))
          exact h_39)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nonempty_x5f_cartesian_x5f_theorem_x2f_statement_x2e_lit
