import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_power_x5f_set_x5f_operation_x5f_closure_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_5 : Litex.In _value_i2 (Litex.powerSet _value_i1)) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_7 : Litex.In _value_i3 (Litex.powerSet _value_i1)), (by
  let _object_w2 := (Litex.union _value_i2 _value_i3)
  exact (by
    let _atomic_wd_1_0 := _object_w2
    let _atomic_wd_1_1 := (Litex.powerSet _value_i1)
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4 _Host_i2 _rep_i2 _value_i2 h_5 _Host_i3 _rep_i3 _value_i3 h_7
          let _object_w2 := (Litex.union _value_i2 _value_i3)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w2
            let _atomic_wd_1_1 := (Litex.powerSet _value_i1)
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    let _atomic_wd_1_1 := (Litex.powerSet _value_i1)
                    exact ((Litex.inPowerSet_iff _atomic_wd_1_0 _value_i1).mpr (Litex.unionSubsetOfBoth _value_i2 _value_i3 _value_i1 ((Litex.inPowerSet_iff _value_i2 _value_i1).mp h_5) ((Litex.inPowerSet_iff _value_i3 _value_i1).mp h_7))))
                )
            )
          exact h_1
        )
      )
  )

theorem h_28 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_30 : Litex.IsSet _value_i4) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_31 : Litex.In _value_i5 (Litex.powerSet _value_i4)) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_33 : Litex.IsSet _value_i6), (by
  let _object_w4 := (Litex.intersect _value_i5 _value_i6)
  exact (by
    let _atomic_wd_1_0 := _object_w4
    let _atomic_wd_1_1 := (Litex.powerSet _value_i4)
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_30 _Host_i5 _rep_i5 _value_i5 h_31 _Host_i6 _rep_i6 _value_i6 h_33
          let _object_w4 := (Litex.intersect _value_i5 _value_i6)
          have h_27 : (by
            let _atomic_wd_1_0 := _object_w4
            let _atomic_wd_1_1 := (Litex.powerSet _value_i4)
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w4
                    let _atomic_wd_1_1 := (Litex.powerSet _value_i4)
                    exact ((Litex.inPowerSet_iff _atomic_wd_1_0 _value_i4).mpr (Litex.intersectSubsetOfLeft _value_i5 _value_i6 _value_i4 ((Litex.inPowerSet_iff _value_i5 _value_i4).mp h_31))))
                )
            )
          exact h_27
        )
      )
  )

theorem h_44 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_46 : Litex.IsSet _value_i7) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_47 : Litex.IsSet _value_i8) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_48 : Litex.In _value_i9 (Litex.powerSet _value_i7)), (by
  let _object_w6 := (Litex.intersect _value_i8 _value_i9)
  exact (by
    let _atomic_wd_1_0 := _object_w6
    let _atomic_wd_1_1 := (Litex.powerSet _value_i7)
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_46 _Host_i8 _rep_i8 _value_i8 h_47 _Host_i9 _rep_i9 _value_i9 h_48
          let _object_w6 := (Litex.intersect _value_i8 _value_i9)
          have h_43 : (by
            let _atomic_wd_1_0 := _object_w6
            let _atomic_wd_1_1 := (Litex.powerSet _value_i7)
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w6
                    let _atomic_wd_1_1 := (Litex.powerSet _value_i7)
                    exact ((Litex.inPowerSet_iff _atomic_wd_1_0 _value_i7).mpr (Litex.intersectSubsetOfRight _value_i8 _value_i9 _value_i7 ((Litex.inPowerSet_iff _value_i9 _value_i7).mp h_48))))
                )
            )
          exact h_43
        )
      )
  )

theorem h_62 : ∀ {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_65 : Litex.IsSet _value_i10) {_Host_i11 : Type v11} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_66 : Litex.In _value_i11 (Litex.powerSet _value_i10)) {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_68 : Litex.IsSet _value_i12), (by
  let _object_w8 := (Litex.setMinus _value_i11 _value_i12)
  exact (by
    let _atomic_wd_1_0 := _object_w8
    let _atomic_wd_1_1 := (Litex.powerSet _value_i10)
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i10 _rep_i10 _value_i10 h_65 _Host_i11 _rep_i11 _value_i11 h_66 _Host_i12 _rep_i12 _value_i12 h_68
          let _object_w8 := (Litex.setMinus _value_i11 _value_i12)
          have h_61 : (by
            let _atomic_wd_1_0 := _object_w8
            let _atomic_wd_1_1 := (Litex.powerSet _value_i10)
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w8
                    let _atomic_wd_1_1 := (Litex.powerSet _value_i10)
                    exact ((Litex.inPowerSet_iff _atomic_wd_1_0 _value_i10).mpr (Litex.setMinusSubsetOfLeft _value_i11 _value_i12 _value_i10 ((Litex.inPowerSet_iff _value_i11 _value_i10).mp h_66))))
                )
            )
          exact h_61
        )
      )
  )

theorem h_80 : ∀ {_Host_i13 : Type v13} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_82 : Litex.IsSet _value_i13) {_Host_i14 : Type v14} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_83 : Litex.In _value_i14 (Litex.powerSet _value_i13)) {_Host_i15 : Type v15} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_85 : Litex.In _value_i15 (Litex.powerSet _value_i13)) {_Host_i16 : Type v16} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_87 : Litex.IsSet _value_i16) (h_78 : Litex.Same _value_i14 _value_i16), (by
  let _object_w10 := (Litex.union _value_i16 _value_i15)
  exact (by
    let _atomic_wd_1_0 := _object_w10
    let _atomic_wd_1_1 := (Litex.powerSet _value_i13)
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i13 _rep_i13 _value_i13 h_82 _Host_i14 _rep_i14 _value_i14 h_83 _Host_i15 _rep_i15 _value_i15 h_85 _Host_i16 _rep_i16 _value_i16 h_87 h_78
          let _object_w10 := (Litex.union _value_i16 _value_i15)
          have h_79 : (by
            let _atomic_wd_1_0 := _object_w10
            let _atomic_wd_1_1 := (Litex.powerSet _value_i13)
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w10
                    let _atomic_wd_1_1 := (Litex.powerSet _value_i13)
                    exact ((Litex.inPowerSet_iff _atomic_wd_1_0 _value_i13).mpr (Litex.unionSubsetOfBoth _value_i16 _value_i15 _value_i13 ((Litex.inPowerSet_iff _value_i16 _value_i13).mp (Litex.inOfSame _value_i14 _value_i16 _atomic_wd_1_1 _atomic_wd_1_1 h_78 (show @Eq M.Value _ _ from Eq.refl _) h_83)) ((Litex.inPowerSet_iff _value_i15 _value_i13).mp h_85))))
                )
            )
          exact h_79
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_power_x5f_set_x5f_operation_x5f_closure_x2f_statement_x2e_lit
