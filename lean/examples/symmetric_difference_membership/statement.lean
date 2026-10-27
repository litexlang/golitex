import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_symmetric_x5f_difference_x5f_membership_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_6 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_7 : Litex.In _value_i3 _value_i1) (h_1 : ¬ Litex.In _value_i3 _value_i2), (by
  let _object_w1 := (Litex.symmetricDifference _value_i1 _value_i2)
  exact (by
    let _atomic_wd_1_1 := _object_w1
    exact Litex.In _value_i3 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 _Host_i2 _rep_i2 _value_i2 h_6 _Host_i3 _rep_i3 _value_i3 h_7 h_1
          let _object_w1 := (Litex.symmetricDifference _value_i1 _value_i2)
          have h_2 : (by
            let _atomic_wd_1_1 := _object_w1
            exact Litex.In _value_i3 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w1
                    exact (Litex.inSymmetricDifferenceLeft _value_i3 _atomic_wd_1_1 h_7 h_1))
                )
            )
          exact h_2
        )
      )
  )

theorem h_28 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_30 : Litex.IsSet _value_i4) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_31 : Litex.IsSet _value_i5) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_32 : Litex.In _value_i6 _value_i5) (h_26 : ¬ Litex.In _value_i6 _value_i4), (by
  let _object_w2 := (Litex.symmetricDifference _value_i4 _value_i5)
  exact (by
    let _atomic_wd_1_1 := _object_w2
    exact Litex.In _value_i6 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_30 _Host_i5 _rep_i5 _value_i5 h_31 _Host_i6 _rep_i6 _value_i6 h_32 h_26
          let _object_w2 := (Litex.symmetricDifference _value_i4 _value_i5)
          have h_27 : (by
            let _atomic_wd_1_1 := _object_w2
            exact Litex.In _value_i6 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w2
                    exact (Litex.inSymmetricDifferenceRight _value_i6 _atomic_wd_1_1 h_26 h_32))
                )
            )
          exact h_27
        )
      )
  )

theorem h_63 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_66 : Litex.IsSet _value_i7) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_67 : Litex.IsSet _value_i8) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_68 : Litex.In _value_i9 _value_i7) (h_61 : Litex.In _value_i9 _value_i8), (by
  let _object_w3 := (Litex.symmetricDifference _value_i7 _value_i8)
  exact (by
    let _atomic_wd_1_1 := _object_w3
    exact ¬ Litex.In _value_i9 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_66 _Host_i8 _rep_i8 _value_i8 h_67 _Host_i9 _rep_i9 _value_i9 h_68 h_61
          let _object_w3 := (Litex.symmetricDifference _value_i7 _value_i8)
          have h_62 : (by
            let _atomic_wd_1_1 := _object_w3
            exact ¬ Litex.In _value_i9 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w3
                    exact (Litex.notInSymmetricDifferenceBoth _value_i9 _atomic_wd_1_1 h_68 h_61))
                )
            )
          exact h_62
        )
      )
  )

theorem h_88 : ∀ {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_89 : Litex.IsSet _value_i10) {_Host_i11 : Type v11} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_90 : Litex.IsSet _value_i11) {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_91 : Litex.IsSet _value_i12) (h_85 : ¬ Litex.In _value_i12 _value_i10) (h_86 : ¬ Litex.In _value_i12 _value_i11), (by
  let _object_w4 := (Litex.symmetricDifference _value_i10 _value_i11)
  exact (by
    let _atomic_wd_1_1 := _object_w4
    exact ¬ Litex.In _value_i12 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i10 _rep_i10 _value_i10 h_89 _Host_i11 _rep_i11 _value_i11 h_90 _Host_i12 _rep_i12 _value_i12 h_91 h_85 h_86
          let _object_w4 := (Litex.symmetricDifference _value_i10 _value_i11)
          have h_87 : (by
            let _atomic_wd_1_1 := _object_w4
            exact ¬ Litex.In _value_i12 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w4
                    exact (Litex.notInSymmetricDifferenceNeither _value_i12 _atomic_wd_1_1 h_85 h_86))
                )
            )
          exact h_87
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_symmetric_x5f_difference_x5f_membership_x2f_statement_x2e_lit
