import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_containment_x5f_monotonicity_x2f_statement_x2e_lit

universe u v1 v2 v3 v6 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_5 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_6 : Litex.IsSet _value_i3) (h_1 : Litex.Subset _value_i1 _value_i2), (by
  let _object_w1 := (Litex.setMinus _value_i1 _value_i3)
  let _object_w2 := (Litex.setMinus _value_i2 _value_i3)
  exact (by
    let _atomic_wd_1_0 := _object_w1
    let _atomic_wd_1_1 := _object_w2
    exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4 _Host_i2 _rep_i2 _value_i2 h_5 _Host_i3 _rep_i3 _value_i3 h_6 h_1
          let _object_w1 := (Litex.setMinus _value_i1 _value_i3)
          let _object_w2 := (Litex.setMinus _value_i2 _value_i3)
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w1
            let _atomic_wd_1_1 := _object_w2
            exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w1
                    let _atomic_wd_1_1 := _object_w2
                    exact (let _subset_left := _atomic_wd_1_0; let _subset_right := _atomic_wd_1_1; Litex.setMinusMono _subset_left.val.left _subset_right.val.left _subset_left.val.right h_1))
                )
            )
          exact h_2
        )
      )
  )

theorem h_24 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_25 : Litex.IsSet _value_i6) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_26 : Litex.IsSet _value_i7) (h_22 : Litex.Subset _value_i6 _value_i7), (by
  let _object_w3 := (Litex.powerSet _value_i6)
  let _object_w4 := (Litex.powerSet _value_i7)
  exact (by
    let _atomic_wd_1_0 := _object_w3
    let _atomic_wd_1_1 := _object_w4
    exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_25 _Host_i7 _rep_i7 _value_i7 h_26 h_22
          let _object_w3 := (Litex.powerSet _value_i6)
          let _object_w4 := (Litex.powerSet _value_i7)
          have h_23 : (by
            let _atomic_wd_1_0 := _object_w3
            let _atomic_wd_1_1 := _object_w4
            exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    let _atomic_wd_1_1 := _object_w4
                    exact (let _subset_left := _atomic_wd_1_0; let _subset_right := _atomic_wd_1_1; Litex.powerSetMono _subset_left.val.bound _subset_right.val.bound h_22))
                )
            )
          exact h_23
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_containment_x5f_monotonicity_x2f_statement_x2e_lit
