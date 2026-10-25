import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_difference_x5f_exclusion_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7 v8
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_5 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_6 : Litex.In _value_i3 _value_i2), (by
  let _object_w1 := (Litex.setMinus _value_i1 _value_i2)
  exact (by
    let _atomic_wd_1_1 := _object_w1
    exact ¬ Litex.In _value_i3 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4 _Host_i2 _rep_i2 _value_i2 h_5 _Host_i3 _rep_i3 _value_i3 h_6
          let _object_w1 := (Litex.setMinus _value_i1 _value_i2)
          have h_1 : (by
            let _atomic_wd_1_1 := _object_w1
            exact ¬ Litex.In _value_i3 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w1
                    exact (let _set := _atomic_wd_1_1; Litex.notInSetMinusOfRight _value_i3 _set.val.left _set.val.right h_6))
                )
            )
          exact h_1
        )
      )
  )

theorem h_14 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_27 : Litex.IsSet _value_i4) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_28 : Litex.IsSet _value_i5) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_29 : Litex.In _value_i6 (Litex.R (M := M))) (h_12 : ¬ Litex.In _value_i6 _value_i4), (by
  let _object_w3 := (Litex.setMinus _value_i4 _value_i5)
  exact (by
    let _atomic_wd_1_1 := _object_w3
    exact ¬ Litex.In _value_i6 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_27 _Host_i5 _rep_i5 _value_i5 h_28 _Host_i6 _rep_i6 _value_i6 h_29 h_12
          let _object_w3 := (Litex.setMinus _value_i4 _value_i5)
          have h_13 : (by
            let _atomic_wd_1_1 := _object_w3
            exact ¬ Litex.In _value_i6 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w3
                    exact (let _set := _atomic_wd_1_1; Litex.notInSetMinusOfLeft _value_i6 _set.val.left _set.val.right h_12))
                )
            )
          exact h_13
        )
      )
  )

theorem h_53 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_54 : Litex.IsSet _value_i7) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_55 : Litex.IsSet _value_i8), (by
  let _object_w4 := (Litex.setMinus _value_i7 _value_i8)
  exact (by
    let _atomic_wd_1_0 := _object_w4
    exact Litex.Subset _atomic_wd_1_0 _value_i7)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_54 _Host_i8 _rep_i8 _value_i8 h_55
          let _object_w4 := (Litex.setMinus _value_i7 _value_i8)
          have h_52 : (by
            let _atomic_wd_1_0 := _object_w4
            exact Litex.Subset _atomic_wd_1_0 _value_i7) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w4
                    exact (let _set := _atomic_wd_1_0; Litex.setMinusSubsetLeft _set.val.left _set.val.right))
                )
            )
          exact h_52
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_difference_x5f_exclusion_x2f_statement_x2e_lit
