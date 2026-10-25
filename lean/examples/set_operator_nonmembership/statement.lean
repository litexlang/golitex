import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_operator_x5f_nonmembership_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7 v8 v9
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_17 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_18 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : ¬ Litex.In _value_i3 _value_i1), (by
  let _object_w2 := (Litex.intersect _value_i1 _value_i2)
  exact (by
    let _atomic_wd_1_1 := _object_w2
    exact ¬ Litex.In _value_i3 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_16 _Host_i2 _rep_i2 _value_i2 h_17 _Host_i3 _rep_i3 _value_i3 h_18 h_1
          let _object_w2 := (Litex.intersect _value_i1 _value_i2)
          have h_2 : (by
            let _atomic_wd_1_1 := _object_w2
            exact ¬ Litex.In _value_i3 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w2
                    exact (let _set := _atomic_wd_1_1; Litex.notInIntersectOfLeft _value_i3 _set.val.left _set.val.right h_1))
                )
            )
          exact h_2
        )
      )
  )

theorem h_34 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_48 : Litex.IsSet _value_i4) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_49 : Litex.IsSet _value_i5) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_50 : Litex.In _value_i6 (Litex.R (M := M))) (h_32 : ¬ Litex.In _value_i6 _value_i5), (by
  let _object_w4 := (Litex.intersect _value_i4 _value_i5)
  exact (by
    let _atomic_wd_1_1 := _object_w4
    exact ¬ Litex.In _value_i6 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_48 _Host_i5 _rep_i5 _value_i5 h_49 _Host_i6 _rep_i6 _value_i6 h_50 h_32
          let _object_w4 := (Litex.intersect _value_i4 _value_i5)
          have h_33 : (by
            let _atomic_wd_1_1 := _object_w4
            exact ¬ Litex.In _value_i6 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w4
                    exact (let _set := _atomic_wd_1_1; Litex.notInIntersectOfRight _value_i6 _set.val.left _set.val.right h_32))
                )
            )
          exact h_33
        )
      )
  )

theorem h_76 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_89 : Litex.IsSet _value_i7) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_90 : Litex.IsSet _value_i8) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_91 : Litex.In _value_i9 (Litex.R (M := M))) (h_73 : ¬ Litex.In _value_i9 _value_i7) (h_74 : ¬ Litex.In _value_i9 _value_i8), (by
  let _object_w6 := (Litex.union _value_i7 _value_i8)
  exact (by
    let _atomic_wd_1_1 := _object_w6
    exact ¬ Litex.In _value_i9 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_89 _Host_i8 _rep_i8 _value_i8 h_90 _Host_i9 _rep_i9 _value_i9 h_91 h_73 h_74
          let _object_w6 := (Litex.union _value_i7 _value_i8)
          have h_75 : (by
            let _atomic_wd_1_1 := _object_w6
            exact ¬ Litex.In _value_i9 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w6
                    exact (let _set := _atomic_wd_1_1; Litex.notInUnion _value_i9 _set.val.left _set.val.right h_73 h_74))
                )
            )
          exact h_75
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_operator_x5f_nonmembership_x2f_statement_x2e_lit
